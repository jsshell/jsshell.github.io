// Javascript Shell

(function (global) {
  "use strict";
  window.addEventListener("load", initialize, false);
  // Capture constructors.
  var O = Object;
  var N = Node;
  var AB = (typeof ArrayBuffer == "function") ? ArrayBuffer : null;
  var F64A = (typeof Float64Array == "function") ? Float64Array : (AB = null);
  var I32A = (typeof Int32Array == "function") ? Int32Array : (AB = null);
  // Capture needed functions.
  var isN = isNaN;
  var isF = isFinite;
  var Oc = O.create;
  var Ogpo = O.getPrototypeOf;
  var Oie = O.isExtensible;
  var Op = O.prototype;
  var Ogopn = O.getOwnPropertyNames;
  var Ogopd = O.getOwnPropertyDescriptor;
  var indirectEval = eval;
  var Js = JSON.stringify;
  var Sfcc = String.fromCharCode;
  var Mp = Math.pow;
  var Mf = Math.floor;
  var Mc = Math.ceil;
  // Convert instance methods to functions expecting 'this' as first arg.
  var call = Function.prototype.call;
  var Ohop = call.bind(O.prototype.hasOwnProperty);
  var Ots = call.bind(O.prototype.toString);
  var Sss = call.bind(String.prototype.substring);
  var St = call.bind(String.prototype.trim);
  var Svo = call.bind(String.prototype.valueOf);
  var Scca = call.bind(String.prototype.charCodeAt);
  var Stuc = call.bind(String.prototype.toUpperCase);
  var Nvo = call.bind(Number.prototype.valueOf);
  var Nts = call.bind(Number.prototype.toString);
  var Bvo = call.bind(Boolean.prototype.valueOf);
  var Aj = call.bind(Array.prototype.join);
  var Ar = call.bind(Array.prototype.reverse);
  var Dvo = call.bind(Date.prototype.valueOf);
  var Dtis = call.bind(Date.prototype.toISOString);
  var Fts = call.bind(Function.prototype.toString);
  var REe = call.bind(RegExp.prototype.exec);
  var Call = call.bind(Function.prototype.call);
  var Apply = call.bind(Function.prototype.apply);

  var lineLength = 80;
  var funcNameMatchRE = /^\s*function\s+([^\(\s]+)\s*\(/;
  var funcSourceMatchRE = /\{([\x00-\uffff]*)\}\s*$/;

  // Whether to expand values by default.
  var expand = false;

  function IsObject(v) {
    return (typeof v == "object") ? (v !== null) : (typeof v == "function");
  }
  function IsFunction(v) { return Ots(v) == "[object Function]"; }
  function IsPlainObject(v) { return Ots(v) == "[object Object]"; }
  function IsArray(v) { return Ots(v) == "[object Array]"; }
  function IsArrayIndex(string) { return string === ("" + (string >> 0)); }
  function GetOwnValue(object, propertyName) {
    var desc = Ogopd(object, propertyName);
    return desc && desc.value;
  }
  function GetValue(object, propertyName) {
    while (object) {
      var desc = Ogopd(object, propertyName);
      if (desc) return desc.value;
      object = Ogpo(object);
    }
  }
  function arrayLike() {
    // Creates an object that looks like an array (numbered
    // elements and a length property). The object has no
    // prototype, so it's safe to read and write elements.
    // Copies any arguments into the object and sets the length.
    var ll = Oc(null);
    ll.length = 0;
    var n = arguments.length;
    for (var i = 0; i < n; i++) {
      ll[i] = arguments[i]
    }
    ll.length = n;
    return ll;
  }

  function className(object) {
    var ots = Ots(object);
    return Sss(ots, 8, ots.length - 1);
  }

  function functionName(func) {
    var name = GetOwnValue(func, "name");
    if (typeof name == "string" && name.length > 0) return name;
    var match = REe(funcNameMatchRE, Fts(func));
    if (match) return match[1];
  }

  function TypeName(v) {
    var result = typeof(v);
    if (result == "string") return "string#" + v.length;
    if (result != "object") return result;
    if (!v) return "null";
    result = className(v);
    if (result == "Object") {
      var own = true;
      var constructor = GetOwnValue(v, "constructor");
      if (typeof constructor != "function") {
        own = false;
        constructor = GetValue(v, "constructor");
      }
      if (typeof constructor == "function") {
        var constructorName = functionName(constructor);
        if (typeof constructorName == "string" && constructorName.length > 0) {
          result = constructorName;
          if (own) result += ".prototype";
        }
      }
    } else {
      switch (result) {
      case "RegExp":
        result += " /" + v.source + "/";
        if (v.global) result += "g";
        if (v.ignoreCase) result += "i";
        if (v.multiline) result += "m";
        break;
      case "Array":
        result += "#" + v.length;
        break;
      case "Number":
        result += "(" + Nvo(v) + ")";
        break;
      case "Boolean":
        result += "(" + Bvo(v) + ")";
        break;
      case "String":
        result += "(" + shortValueToString(Svo(v)) + ")";
        break;
      case "Date":
        result += "(" + Dtis(v) + ")";
        break;
      }
      result = "<" + result + ">";
    }
    return result;
  }

  var resultCount = 0;

  function assignAttributes(dst, src) {
    var names = Ogopn(src);
    for (var i = 0; i < names.length; i++) {
      var name = names[i];
      var value = GetOwnValue(src, name);
      if (IsPlainObject(value)) {
        var prop = dst[name];
        // Copy recursively.
        assignAttributes(prop, value);
      } else if (typeof value == "function") {
        dst.addEventListener(name, value, false);
      } else {
        dst[name] = value;
      }
    }
  }

  function addChild(element, childSpec) {
    if (childSpec == null) return;
    if (IsArray(childSpec)) {
      childSpec = Apply(DOM, null, childSpec);
    }
    if (childSpec instanceof N) {
      element.appendChild(childSpec);
      return;
    }
    childSpec = "" + childSpec;
    element.appendChild(document.createTextNode(childSpec));
  }

  // -------------------------------------------------------------------
  // DOM helper functions.
  function TXT(string) {
    return document.createTextNode(string);
  }

  // |tag| must be a string.
  // |attrs|, if present, must be a non-array, non-DOM object.
  // |children| may be either a DOM Node, DocumentFragment, string or array
  //    any of any of these.
  function DOM(tag, attrs, children /*...*/) {
    var parts = tag.split(/([#.])/g);
    tag = parts[0];
    var element = document.createElement(tag);
    var classNames = arrayLike();
    for (var i = 1; i < parts.length; i += 2) {
      if (parts[i] == '.') {
        classNames[classNames.length++] = parts[i + 1];
      } else {
        element.id = parts[i + 1];
      }
    }
    element.className = Aj(classNames, " ");
    var childIndex = 1;
    if (IsPlainObject(attrs)) {
      assignAttributes(element, attrs);
      childIndex++;
    }

    while (childIndex < arguments.length) {
      var child = arguments[childIndex];
      addChild(element, child);
      childIndex++;
    }
    return element;
  }

  function areaWrap(string) {
    if (string.length < 80) return string;
    var lines = Mc(string.length / 80);
    return DOM("textarea.jsshell-inlineText",
                { cols : 80,
                  rows : lines,
                  value : string,
                  readOnly : true });
  }

  function initialize() {
    document.body.appendChild(DOM("h1.jsshell-headline", "JSShell"));
    var inputArea = createInput();
    document.body.appendChild(inputArea);
    var inputField = inputArea.getElementsByTagName("textarea")[0];
    var cmdline = decodeURIComponent(location.search.substring(1));
    inputField.value = cmdline;
    inputField.focus();
    inputField.select();
  }

  function executeInput(input, use_eval) {
    var text = St(input.value);
    if (text.length == 0) return;
    inputHistory.add(text);
    document.body.insertBefore(DOM("div.jsshell-inputlog",
                                   text),
                               document.body.lastChild);
    if (use_eval) {
      evalblock: {
        try {
          var value = indirectEval(text);
        } catch (exn) {
          reportException(exn);
          break evalblock;
        }
        if (Ots(value) !== "[object Undefined]") reportValue(value);
      }
    } else {
      var script = DOM("script");
      script.textContent = text;
      document.body.insertBefore(script, document.body.lastChild);
    }

    input.style.width = null;
    input.style.height = null;
    input.focus();
    input.select();
    input.scrollIntoView();
  }

  function insertHTML(input) {
    var text = input.value;
    var div = document.createElement("div");
    div.innerHTML = text;
    var first = div.firstChild;
    while (div.firstChild) {
      document.body.insertBefore(div.firstChild, document.body.lastChild);
    }
    reportValue(first);
  }

  function insertIFrame(input) {
    var frame = DOM("iframe", {src:
        "javascript:top.document.getElementById('jsshell-input-id').value"});
    document.body.insertBefore(frame, document.body.lastChild);
    reportValue(frame);
  }

  // Page visible shell-specific namespace exposing
  // the log function.
  global.shell = { log: reportValue };

  // -------------------------------------------------------------------
  // HISTORY

  var inputHistory = arrayLike();
  inputHistory.position = 0;
  inputHistory.add = function (value) {
    if (this.length === 0 || this[this.length - 1] != value) {
      this[this.length++] = value;
    }
    this.position = this.length;
  };
  inputHistory.go = function(input, direction) {
    var newPosition = this.position + direction;
    if (newPosition < 0 || newPosition > this.length) return;
    if (this.position == this.length) {
      this[this.length] = input.value;
      if (this[newPosition] == input.value) {
        newPosition -= 1;
        if (newPosition < 0) return;
      }
    }
    input.value = this[newPosition];
    if (newPosition == this.length - 1 &&
      this[newPosition] == this[this.length]) {
      newPosition = this.length;
    }
    this.position = newPosition;
  };

  // -------------------------------------------------------------------
  // INPUT

  function createInput() {
    return DOM("div", {className: "jsshell" },
               ["textarea", { className: "jsshell-input",
                              id: "jsshell-input-id",
                              rows: 1,
                              cols: lineLength,
                              wrap: "hard",
                              keyup: inputKeyUp }],
               ["br"],
               ["button", { className:
                                "jsshell-button jsshell-default-button",
                            type: "button",
                            title: "eval the input in the global scope" +
                                   " (Ctrl-Return)",
                            click: evalButtonClick },
                          "Evaluate"],
               ["button", { className: "jsshell-button",
                            type: "button",
                            title: "Execute input as script" +
                                   " (Shift-Ctrl-Return)",
                            click: executeButtonClick },
                          "Execute"],
               ["button", { className: "jsshell-button",
                            type: "button",
                            title: "Insert input as HTML in page",
                            click: insertHTMLButtonClick },
                          "Insert HTML"],
               ["button.jsshell-button", {
                          type: "button",
                          title:"Insert input as content of a new iframe",
                          click: insertIFrameButtonClick },
                        "Insert iframe"],
               ["label", {htmlFor: "jsshell-expand",
                          title: "Expand some values as default"},
                         ["button.jsshell-button#jsshell-expand", {
                             type: "button",
                             click: function () {
                               expand = !expand;
                               this.innerHTML = expand ? "&check;" : "&nbsp";
                             }}, "\xA0"],
                         "Expand"]);
  }

  function inputKeyUp(evt) {
    if (evt.ctrlKey) {
      if (evt.keyCode == 13) {
        // C-Ret (eval) or S-C-Ret (execute).
        executeInput(this, !evt.shiftKey);
        return;
      }
      if (evt.keyCode == 38) {  // Cursor up.
        inputHistory.go(this, -1);
      } else if (evt.keyCode == 40) { // Cursor down.
        inputHistory.go(this, 1);
      }
    }
    // Check for lines of input.
    var self = this;
    setTimeout(function(){
                 var text = self.value;
                 var lineCount = 0;
                 var i = 0;
                 var prev = 0;
                 do {
                   lineCount++;
                   i = text.indexOf("\n", i) + 1;
                   if (i > 0) {
                     if (i - prev > lineLength) {
                       lineCount += ((i - prev) / lineLength) | 0;
                     }
                     prev = i;
                   }
                 } while (i > 0);
                 if (text.length - prev > lineLength) {
                   lineCount += ((text.length - prev) / lineLength) | 0;
                 }
                 if (self.rows != lineCount) self.rows = lineCount;
               }, 0);
  }

  function evalButtonClick(evt) {
    var input = this.parentNode.firstChild;
    executeInput(input, true);
  }

  function executeButtonClick(evt) {
    var input = this.parentNode.firstChild;
    executeInput(input, false);
  }

  function insertHTMLButtonClick(evt) {
    var input = this.parentNode.firstChild;
    insertHTML(input);
  }

  function insertIFrameButtonClick(evt) {
    var input = this.parentNode.firstChild;
    insertIFrame(input);
  }

  // -------------------------------------------------------------------
  // OUTPUT

  function reportValue(value) {
    var key = "$" + (++resultCount);
    global[key] = value;
    function clean(evt) {
      delete global[key];
      this.parentNode.parentNode.removeChild(this.parentNode);
    }
    document.body.insertBefore(DOM("div.jsshell-property",
                                   ["span.jsshell-remove",
                                        { click: clean }, "[x]"],
                                   ["span.jsshell-property-key",
                                       key],
                                   ["span.jsshell-property-eq", " = "],
                                   displayValue(value)),
                               document.body.lastChild);
  }

  function reportException(value) {
    document.body.insertBefore(DOM("div", "" + value, ["br"],
                                   ["pre", value.stack]),
                               document.body.lastChild);
  }

  function displayStringCollapsed(v) {
    var slice = Sss(v, 0, 72);
    var pretty = Js(slice);
    function expandString(evt) {
      this.removeEventListener("click", expandString, false);
      this.parentNode.parentNode.replaceChild(displayStringExpanded(v),
                                              this.parentNode);
    }
    return DOM("span", ["span.jsshell-string", pretty],
               ["span.jsshell-expand", { click: expandString }, "..."]);
  }

  function displayStringExpanded(v) {
    function collapseString(evt) {
      this.removeEventListener("click", collapseString, false);
      this.parentNode.parentNode.replaceChild(displayStringCollapsed(v),
                                              this.parentNode);
    }
    var N = 16;
    var surrogate = false;
    var table = DOM("table.jsshell-chartable");

    for (var i = 0; i < v.length; i += N) {
      var row = table.insertRow(table.rows.length);
      var header = row.insertCell(0);
      header.className="jsshell-chartable-offset";
      header.appendChild(TXT(Nts(i, 16)));
      for (var j = 0; j < N; j++) {
        var charCell = row.insertCell(1 + j * 2)
        var codeCell = row.insertCell(1 + j);
        codeCell.className = "jsshell-chartable-code";
        charCell.className = "jsshell-chartable-char";
        if (j === 0) {
          codeCell.className += " jsshell-firstcol";
          charCell.className += " jsshell-firstcol";
        } else if ((j & 3) == 0) {
          codeCell.className += " jsshell-fourthcol";
          charCell.className += " jsshell-fourthcol";
        }
        if (j === N - 1) {
          codeCell.className += " jsshell-lastcol";
          charCell.className += " jsshell-lastcol";
        }
        if (i + j == v.length) {
          charCell.colSpan = N - j;
          charCell.className += " jsshell-lastcol jsshell-empty";
          codeCell.colSpan = N - j;
          codeCell.className += " jsshell-lastcol jsshell-empty";
          break;
        } 
        var code = Scca(v, i + j);
        codeCell.appendChild(TXT(Nts(code, 16)));
        // TODO: Only do this for printable chars.
        charCell.appendChild(TXT(Sfcc(code)));
        (function(charCell, codeCell) {

          codeCell.addEventListener("mouseover", function (e) {
            var cn = charCell.className;
            charCell.className = cn + " jsshell-highlight";
            function onmouseout(e) {
              charCell.className = cn;
              codeCell.removeEventListener("mouseout", onmouseout, false);
            };
            codeCell.addEventListener("mouseout", onmouseout, false);
          }, false);
          charCell.addEventListener("mouseover", function (e) {
            var cn = codeCell.className;
            codeCell.className = cn + " jsshell-highlight";
            function onmouseout(e) {
              codeCell.className = cn;
              charCell.removeEventListener("mouseout", onmouseout, false);
            };
            charCell.addEventListener("mouseout", onmouseout, false);
          }, false);
        })(charCell, codeCell);
      }
    }
    return DOM("span", ["span.jsshell-string", table], ["br"],
                       " (", ["span.jsshell-collapse",
                                  {click: collapseString },
                                  "collapse"], ")");
  }

  function displayNumberCollapsed(v) {
    function expandNumber(evt) {
      this.removeEventListener("click", expandNumber, false);
      this.parentNode.parentNode.replaceChild(displayNumberExpanded(v),
                                              this.parentNode);
    }
    var result = DOM("span", ["span.jsshell-number", Nts(v)], " ",
                       ["span.jsshell-expand",
                          { click: expandNumber }, "..."]);
    return result;
  }

  function displayNumberExpanded(v) {
    function collapseNumber(evt) {
      this.removeEventListener("click", collapseNumber, false);
      this.parentNode.parentNode.replaceChild(displayNumberCollapsed(v),
                                              this.parentNode);
    }
    var result = DOM("span", " (", ["span.jsshell-collapse",
                            { click: collapseNumber }, "collapse"], ")",
                            ["br"], numberDetails(v), ["br"],
                            ["span.jsshell-number", Nts(v)]);
    return result;
  }

  function numberDetails(v) {
    var bits = Double.from(v);
    function colorizeHex(bits) {
      var hexString = bits.toHexString();
      return DOM("span",
          ["span.jsshell-hexsign", hexString[0]],
          ["span.jsshell-hexexponent", Sss(hexString,1,3)],
          ["span.jsshell-hexmantissa", Sss(hexString, 3)]);
    }
    function colorizeBin(bits) {
      var binString = bits.toBinaryString();
      return DOM("span",
          ["span.jsshell-binsign", binString[0]],
          ["span.jsshell-binexponent", Sss(binString, 1, 12)],
          ["span.jsshell-binmantissa", Sss(binString, 12)]);
    }
    if (v == (v & 0x1fffff) && v <= 0x10FFFF && (v < 0xD800 || v > 0xDFFF)) {
      var char;
      if (v < 0x10000) {
        char =  Sfcc(v);
      } else {
        var surrogateBits = v - 0x10000;
        char = Sfcc(0xD800 + (surrogateBits & 0x3ff), 
                    0xDC00 + (surrogateBits >> 10));
      }
      return DOM("table.jsshell-numbers",
         ["tr",["th", "Hex"], ["td", areaWrap(Nts(+bits, 16))]],
         ["tr",["th", "Character"], ["td", areaWrap(Js(char))]],
         ["tr",["th", "Exact"], ["td", areaWrap(bits.toExactString())]],
         ["tr",["th", "Bits (hex)"], ["td", colorizeHex(bits)]],
         ["tr",["th", "Bits (binary)"], ["td", colorizeBin(bits)]]);

    }
    return DOM("table.jsshell-numbers",
       ["tr",["th", "Hex"], ["td", areaWrap(Nts(+bits, 16))]],
       ["tr",["th", "Exact"], ["td", areaWrap(bits.toExactString())]],
       ["tr",["th", "Bits (hex)"], ["td", colorizeHex(bits)]],
       ["tr",["th", "Bits (binary)"], ["td", colorizeBin(bits)]]);
  }

  function prettyPrintPrimitive(v) {
    if (typeof v === "string") {
      if (expand) return displayStringExpanded(v);
      return displayStringCollapsed(v);
    } else if (typeof v === "number") {
      if (expand) return displayNumberExpanded(v);
      return displayNumberCollapsed(v);
    } else {
      return "" + v;
    }
  }

  function displayValue(value) {
    var res;
    if (!IsObject(value)) {
      res = DOM("span",
                prettyPrintPrimitive(value));
    } else if (IsArray(value)) {
      res = DOM("span",
                "[", displayObjectCollapsed(value), "]");
    } else if (IsFunction(value)) {
      res = DOM("span",
                "function ", functionName(value), "() {",
                displayFunctionSourceCollapsed(value), "}",
                displayObjectCollapsed(value));
      return res;
    } else {
      res = DOM("span",
                "{", displayObjectCollapsed(value), "}");
    }
    res.appendChild(DOM("span.jsshell-typename",
                        " : ", TypeName(value)));
    return res;
  }

  function shortValueToString(value) {
    switch (typeof value) {
    case "string":
      if (value.length > 10) {
        value = Sss(value, 0, 7) + "...";
      }
      return Js(value);
    case "object":
      if (value !== null) {
        return "<" + typeName(value) + ">";
      }
      // Fallthrough on null.
    case "number":
    case "bool":
      return "" + value;
    case "undefined":
      return "";
    case "function":
      return "<function>";
    default:
      return "<" + (typeof value) + ">";
    }
  }

  function displayFunctionSourceCollapsed(func) {
    // TODO: Make it possible to expand source from function's toString.
    return TXT("...");
  }

  function displayObjectCollapsed(object) {
    // TODO: Show a (noninteractive) preview of the first few properties.
    function expand(evt) {
      this.removeEventListener("click", expand, false);
      this.parentNode.replaceChild(displayObject(object), this);
    }

    var result = DOM("span", {className:"jsshell-expand",
                              click: expand }, "...");
    return result;
  }

  function displayObject(object) {
    // TODO: Allow progressive display of objects with many properties.
    function collapse(evt) {
      this.removeEventListener(this, collapse, false);
      this.parentNode.parentNode.replaceChild(displayObjectCollapsed(object),
                                              this.parentNode);
    }
    var list = DOM("span", {className:"jsshell-value-list"},
                   DOM("span", {className:"jsshell-collapse",
                                click: collapse}, " (collapse) "));
    var proto = Ogpo(object);
    if (proto) {
      list.appendChild(displayPseudoProperty("[[Prototype]]", proto));
    }

    if (!Oie(object)) {
      list.appendChild(displayPseudoProperty("[[Extensibe]]", false));
    }

    var primitiveValue;
    switch (Ots(object)) {
    case "[object String]":
      primitiveValue = Svo(object);
      break;
    case "[object Number]":
      primitiveValue = Nvo(object);
      break;
    case "[object Boolean]":
      primitiveValue = Bvo(object);
      break;
    case "[object Date]":
      primitiveValue = Dvo(object);
      break;
    }
    if (primitiveValue !== void 0) {
      list.appendChild(displayPseudoProperty("[[PrimitiveValue]]",
                                             primitiveValue));
    }

    var keys = Ogopn(object);
    for (var i = 0; i < keys.length; i++) {
      var key = keys[i];
      list.appendChild(displayProperty(object, key));
    }
    return list;
  }

  function displayPseudoProperty(key, value) {
    return DOM("div", {className:"jsshell-property"},
               DOM("span", {className:"jsshell-property-key"}, key),
               " : ",
               displayValue(value));
  }

  function displayProperty(object, key) {
    var line = DOM("div",{className: "jsshell-property"});
    var keyText = DOM("span",
                      {className: "jsshell-property-key"},
                      key);
    line.appendChild(keyText);
    var desc = Ogopd(object, key);
    var props = [];
    if (desc.enumerable) props.push("enumerable");
    if (desc.configurable) props.push("configurable");

    if ("value" in desc) {
      if (desc.writable) props.push("writable");
      line.appendChild(TXT(" : "));
      line.appendChild(displayValue(desc.value));
    } else {
      var getset = [];
      if (typeof desc.get == "function") { getset.push("get") };
      if (typeof desc.set == "function") { getset.push("set") };
      // TODO: Display getter and setter as functions.
      line.appendChild(TXT("<" + getset.join("/") + ">"));
    }
    keyText.title = props.join(", ");
    return line;
  }

  // JS Double Tool
  function Double(negative, biasedExponent, mantissaBits, value) {
    this.negative = negative;
    this.biasedExponent = biasedExponent;
    this.mantissaBits = mantissaBits;
    this.value = value;
  }

  Double.prototype = {
    constructor: Double,
    toString: function toString() {
      var double = this.valueOf();
      if (double == 0 && this.negative) return "-0";
      return Nts(double);
    },
    valueOf: function valueOf() {
      if (typeof this.value === "number") return this.value;
      if (typeof AB == "function") {
        var a = new AB(8);
        var i = new I32A(a);
        i[0] = this.mantissaBits >> 0;
        i[1] = Mf(this.mantissaBits / 0x100000000) |
               this.biasedExponent << 20 |
               (this.negative ? 0x80000000 : 0);
        var d = new F64A(a);
        return this.value = d[0];
      }
      // Generate doubles arithmetically. Doesn't handle NaN payloads.
      if (!this.isFinite()) {
        if (this.isNaN()) {
          this.value == NaN;
        } else {
          this.value = (this.negative ? -Infinity : Infinity);
        }
      } else {
        this.value = this.sign * Mp(2, this.exponent) * this.mantissa;
      }
      return this.value;
    },
    toHexString: function toHexString() {
      var exp = this.biasedExponent;
      if (this.negative) exp += Mp(2, Double.exponentBits);
      exp += Mp(2, Double.exponentBits + 1);
      // This assumes Double.mantissaBits is a multiplum of 4.
      var mantissa = this.mantissaBits + Mp(2, Double.mantissaBits);
      var expString = Stuc(Sss(Nts(exp, 16),1));
      var mantissaString = Stuc(Sss(Nts(mantissa, 16), 1));
      return expString + mantissaString;
    },
    toBinaryString: function toBinaryString() {
      var exp = this.biasedExponent;
      if (this.negative) exp += Mp(2, Double.exponentBits);
      exp += Mp(2, Double.exponentBits + 1);
      var mantissa = this.mantissaBits + Mp(2, Double.mantissaBits);
      var expString = Nts(exp, 2).substring(1);
      var mantissaString = Sss(Nts(mantissa, 2), 1);
      return expString + mantissaString;
    },
    toExactString: function toExactString(exponential_opt) {
      function i2d(i) {
        // positive integer to decimal.
        var res = arrayLike(0);
        var pow2 = arrayLike(1);

        function add() {
          var carry = 0;
          var n = res.length;
          if (n < pow2.length) n = pow2.length;
          for (var i = 0; i < n; i++) {
            var d = (res[i] || 0) + (pow2[i] || 0) + carry;
            carry = 0;
            if (d >= 10) {
              carry = 1;
              d -= 10;
            }
            res[i] = d;
          }
          if (carry > 0) res[i++] = carry;
          res.length = i;
        }
        function double() {
          var carry = 0;
          for (var i = 0; i < pow2.length; i++) {
            var d = pow2[i] * 2 + carry;
            carry = 0;
            if (d >= 10) {
              carry = 1;
              d -= 10;
            }
            pow2[i] = d;
          }
          if (carry > 0) pow2[i++] = carry;
          pow2.length = i;
        }
        while (i > 0) {
          if (i & 1) {
            add();
            i -= 1;
          }
          double();
          i /= 2;
        }
        return Aj(Ar(res),"");
      }
      function f2d(f) {
        // Fraction (between zero and one) to decimal.
        var res = arrayLike(0);
        var frac = arrayLike(5); // 0.5
        function halve() {
          var carry = 0;
          for (var i = 0; i < frac.length; i++) {
            var d = frac[i];
            frac[i] = (d >> 1) + carry;
            carry = (d & 1) * 5;
          }
          if (carry > 0) frac[i++] = carry;
          frac.length = i;
        }
        function add() {
          var carry = 0;
          for (var i = frac.length - 1; i >= 0; i--) {
            var d = (res[i] || 0) + frac[i] + carry;
            carry = 0;
            if (d >= 10) {
              carry = 1;
              d -= 10;
            }
            res[i] = d;
          }
          res.length = frac.length;
        }
        while (f > 0) {
          f = f * 2;
          if (f & 1) {
            add();
            f -= 1;
          }
          halve()
        }
        return Aj(res, "");
      }

      var quietFlag = Mp(2,51);
      if (this.isNaN()) {
        // NaN payload is lost when converting to number.
        if (this.negative || this.mantissaBits != quietFlag) {
          // Non-standard NaN created using Double.fromBits.
          var str = "SNaN";
          var mantissaBits = this.mantissaBits;
          if (mantissaBits >= quietFlag) {
            str = "QNaN";
            mantissaBits -= quietFlag;
          }
          return str + "(" + (this.negative ? "-" : "") +
                       Stuc(Nts(mantissaBits, 16)) + ")";
        }
        return "NaN";
      }
      var d = this.valueOf();
      if (d == 0) {
        if (1/d < 0) return "-0.0";
        return "0.0";
      }
      var sign = "";
      if (d < 0) {
        sign = "-";
        d = -d;
      }
      if (!isFinite(d)) return sign + "Infinity";
      var intPart = Mf(d);
      var fracPart = d - intPart;
      if (exponential_opt && (intPart == 0) != (fracPart == 0)) {
        if (intPart >= 1e21) return makeIntExp(sign, intPart);
        if (fracPart != 0 && fracPart < 1e-6) return makeFracExp(sign, fracPart);
      }
      return sign + i2d(intPart) + "." + f2d(fracPart);

      function makeIntExp(sign, intPart) {
        var intString = i2d(intPart);
        var n = intString.length;
        var nonZeroCount = n;
        while (Scca(intString, nonZeroCount - 1) == 0x30) {
          nonZeroCount--;
        }
        var res = intString[0];
        if (nonZeroCount >  1) {
          res += "." + Sss(intString, 1, nonZeroCount);
        }
        res += "e+" + (n - 1);
        return res;
      }

      function makeFracExp(sign, fracPart) {
        var fracString = f2d(fracPart);
        var n = fracString.length;
        var zeroCount = 0;
        while (Scca(fracString, zeroCount) == 0x30) zeroCount++;

        var res = fracString[zeroCount];
        if (zeroCount + 1 < n) {
          res += "." + Sss(fracString, zeroCount + 1);
        }
        res += "e-" + (zeroCount + 1);
        return res;
      }

    },
    isFinite: function isFinite() {
      return this.biasedExponent < 0x7FF;
    },
    isNaN: function isNaN() {
      return this.biasedExponent == 0x7FF && this.mantissaBits != 0;
    },
    isDenormal: function isDenormal() {
      return this.biasedExponent == 0;
    },
    get exponent() {
      if (this.biasedExponent == 0x7FF) {
        return this.value;
      }
      if (this.biasedExponent == 0) return -Double.bias + 1;
      return this.biasedExponent - Double.bias;
    },
    get mantissa() {
      // If NaN, return payload.
      if (this.biasedExponent == 0x7ff) return mantissaBits;
      var mantissa = this.mantissaBits / Mp(2, Double.mantissaBits);
      if (this.biasedExponent > 0) mantissa += 1;
      return mantissa;
    },
    get sign() {
      return this.negative ? -1 : 1;
    }
  };

  Double.mantissaBits = 52;
  Double.exponentBits = 11;
  Double.bias = 1023;

  Double.NegativeZero = new Double(true, 0, 0, -0);
  Double.Zero = new Double(false, 0, 0, 0);
  Double.MinValue = new Double(false, 0, 1, 5e-324);
  Double.MinNormal = new Double(false, 1, 0, 2.2250738585072014e-308);
  Double.NaN = new Double(false, 0x7FF, 0x8000000000000, NaN);
  Double.Infinity = new Double(false, 0x7FF, 0, Infinity);
  Double.NegativeInfinity = new Double(true, 0x7FF, 0, -Infinity);

  Double.from = function from(double) {
    function fromUsingTypedArray(double) {
      var a = new AB(8);
      var d = new F64A(a);
      d[0] = double;
      var i = new I32A(a);
      var low = i[0];
      var hi = i[1];
      var negative = hi < 0;
      var mantissabits = (low >>> 0) + (hi & 0xfffff) * Mp(2,32);
      var biasedExponent = (hi >>> 20) & 0x7ff;
      return new Double(negative, biasedExponent, mantissabits, double);
    }
    if (AB !== null) {
      return fromUsingTypedArray(double);
    }
    // Slow arithmetic decomposition of double value.
    if (!isF(double)) {
      if (isN(double)) return Double.NaN;
      if (double < 0) return Double.NegativeInfinity;
      return Double.Infinity;
    }
    var magnitude = double;
    var negative = false;
    if (magnitude < 0 || magnitude == 0 && 1 / magnitude < 0) {
      negative = true;
      magnitude = -magnitude;
    }
    var minNormal = 2.2250738585072014e-308;
    if (magnitude < minNormal) {
      // It's a denormal (including zero).
      var mantissaBits =
         magnitude * Mp(2, Double.bias) * Mp(2, Double.mantissaBits - 1);
      return new Double(negative, 0, mantissaBits, double);
    }
    var exponent = 0;
    while (magnitude < 1) {
      magnitude *= 2;
      exponent -= 1;
    }
    while (magnitude >= 2) {
      magnitude /= 2;
      exponent += 1;
    }
    var mantissaBits = (magnitude - 1) * Mp(2, Double.mantissaBits);
    return new Double(negative, exponent + Double.bias, mantissaBits, double);
  };

  Double.fromBits =
      function fromBits(negative, biasedExponent, mantissaBits, value) {
    if ((typeof biasedExponent != "number") ||
        (typeof mantissaBits != "number") ||
        !(biasedExponent >= 0 && biasedExponent <= 0x7ff) ||
        !(mantissaBits >= 0 && mantissaBits < 4503599627370496)) {
      return Double.NaN;
    }
    negative = !!negative;
    if (biasedExponent == 0x7FF) {
      if (mantissaBits == 0) {
        if (negative) return Double.NegativeInfinity;
        return Double.Infinity;
      }
    }
    if (typeof value != "number") value = void 0;
    return new Double(negative, biasedExponent, mantissaBits, value);
  }
})(this);
