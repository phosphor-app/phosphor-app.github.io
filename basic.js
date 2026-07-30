/* PFBasic — a small structured-BASIC interpreter that runs entirely in the browser.
   Modeled on the MY-BASIC dialect PyForge uses: no line numbers required.
   Supports: REM/' comments, PRINT (, and ; separators), LET / bare assignment,
   INPUT (reads from the stdin box), IF/THEN/ELSEIF/ELSE/ENDIF (block and one-line),
   FOR/TO/STEP/NEXT, WHILE/WEND, GOTO <label>, labels (name:), END.
   Expressions: + - * / MOD ^, unary -, comparisons (= <> < > <= >=), AND OR NOT,
   string concatenation with +, and functions ABS INT RND SQR SIN COS TAN LEN
   LEFT RIGHT MID STR VAL CHR ASC UCASE LCASE.  PFBasic.run(src, stdin) -> {out}. */
(function (global) {
  var MAX_STEPS = 2000000;

  function run(source, stdin) {
    var out = [];
    var emit = function (s) { out.push(s); };
    var inLines = String(stdin || "").split(/\r?\n/);
    var inPos = 0;
    var vars = Object.create(null);
    var rndState = 123456789 >>> 0;
    function rnd() { rndState = (1103515245 * rndState + 12345) >>> 0; return rndState / 4294967296; }

    // ---- tokenize a whole line into tokens (numbers, strings, names, ops) ----
    function lex(line) {
      var toks = [], i = 0, n = line.length;
      while (i < n) {
        var c = line[i];
        if (c === " " || c === "\t") { i++; continue; }
        if (c === '"') {
          var j = i + 1, s = "";
          while (j < n && line[j] !== '"') { s += line[j]; j++; }
          toks.push({ t: "str", v: s }); i = j + 1; continue;
        }
        if (/[0-9]/.test(c) || (c === "." && /[0-9]/.test(line[i + 1] || ""))) {
          var num = ""; while (i < n && /[0-9.]/.test(line[i])) { num += line[i]; i++; }
          toks.push({ t: "num", v: parseFloat(num) }); continue;
        }
        if (/[A-Za-z_]/.test(c)) {
          var id = ""; while (i < n && /[A-Za-z0-9_$]/.test(line[i])) { id += line[i]; i++; }
          toks.push({ t: "name", v: id }); continue;
        }
        var two = line.substr(i, 2);
        if (two === "<=" || two === ">=" || two === "<>") { toks.push({ t: "op", v: two }); i += 2; continue; }
        toks.push({ t: "op", v: c }); i++;
      }
      return toks;
    }

    // ---- expression parser (recursive descent over a token array) ----
    function Expr(toks) { this.toks = toks; this.p = 0; }
    Expr.prototype.peek = function () { return this.toks[this.p]; };
    Expr.prototype.next = function () { return this.toks[this.p++]; };
    Expr.prototype.isKw = function (w) { var t = this.peek(); return t && t.t === "name" && t.v.toUpperCase() === w; };
    Expr.prototype.parse = function () { return this.orExpr(); };
    Expr.prototype.orExpr = function () {
      var a = this.andExpr();
      while (this.isKw("OR")) { this.next(); var b = this.andExpr(); a = (truthy(a) || truthy(b)) ? 1 : 0; }
      return a;
    };
    Expr.prototype.andExpr = function () {
      var a = this.notExpr();
      while (this.isKw("AND")) { this.next(); var b = this.notExpr(); a = (truthy(a) && truthy(b)) ? 1 : 0; }
      return a;
    };
    Expr.prototype.notExpr = function () {
      if (this.isKw("NOT")) { this.next(); return truthy(this.notExpr()) ? 0 : 1; }
      return this.cmp();
    };
    Expr.prototype.cmp = function () {
      var a = this.add();
      var t = this.peek();
      if (t && t.t === "op" && ["=", "<>", "<", ">", "<=", ">="].indexOf(t.v) >= 0) {
        this.next(); var b = this.add();
        switch (t.v) {
          case "=": return eq(a, b) ? 1 : 0;
          case "<>": return eq(a, b) ? 0 : 1;
          case "<": return a < b ? 1 : 0;
          case ">": return a > b ? 1 : 0;
          case "<=": return a <= b ? 1 : 0;
          case ">=": return a >= b ? 1 : 0;
        }
      }
      return a;
    };
    Expr.prototype.add = function () {
      var a = this.mul();
      for (;;) {
        var t = this.peek();
        if (t && t.t === "op" && (t.v === "+" || t.v === "-")) {
          this.next(); var b = this.mul();
          if (t.v === "+") a = (typeof a === "string" || typeof b === "string") ? (toStr(a) + toStr(b)) : (a + b);
          else a = a - b;
        } else break;
      }
      return a;
    };
    Expr.prototype.mul = function () {
      var a = this.pow();
      for (;;) {
        var t = this.peek();
        if (t && t.t === "op" && (t.v === "*" || t.v === "/")) { this.next(); var b = this.pow(); a = t.v === "*" ? a * b : a / b; }
        else if (this.isKw("MOD")) { this.next(); var m = this.pow(); a = a % m; }
        else break;
      }
      return a;
    };
    Expr.prototype.pow = function () {
      var a = this.unary();
      if (this.peek() && this.peek().t === "op" && this.peek().v === "^") { this.next(); return Math.pow(a, this.pow()); }
      return a;
    };
    Expr.prototype.unary = function () {
      var t = this.peek();
      if (t && t.t === "op" && t.v === "-") { this.next(); return -this.unary(); }
      if (t && t.t === "op" && t.v === "+") { this.next(); return this.unary(); }
      return this.primary();
    };
    Expr.prototype.primary = function () {
      var t = this.next();
      if (!t) throw new Error("unexpected end of expression");
      if (t.t === "num") return t.v;
      if (t.t === "str") return t.v;
      if (t.t === "op" && t.v === "(") { var v = this.orExpr(); var c = this.next(); if (!c || c.v !== ")") throw new Error("missing )"); return v; }
      if (t.t === "name") {
        var nm = t.v.toUpperCase();
        if (this.peek() && this.peek().t === "op" && this.peek().v === "(") {
          this.next(); var args = [];
          if (!(this.peek() && this.peek().v === ")")) {
            args.push(this.orExpr());
            while (this.peek() && this.peek().v === ",") { this.next(); args.push(this.orExpr()); }
          }
          var cl = this.next(); if (!cl || cl.v !== ")") throw new Error("missing ) after " + nm);
          return callFn(nm, args);
        }
        if (nm === "TRUE") return 1; if (nm === "FALSE") return 0; if (nm === "PI") return Math.PI;
        var key = t.v.toUpperCase();
        return (key in vars) ? vars[key] : 0;
      }
      throw new Error("unexpected token '" + (t.v) + "'");
    };

    function callFn(nm, a) {
      switch (nm) {
        case "ABS": return Math.abs(a[0]);
        case "INT": return Math.floor(a[0]);
        case "SGN": return a[0] > 0 ? 1 : a[0] < 0 ? -1 : 0;
        case "SQR": return Math.sqrt(a[0]);
        case "SIN": return Math.sin(a[0]);
        case "COS": return Math.cos(a[0]);
        case "TAN": return Math.tan(a[0]);
        case "RND": return rnd() * (a.length ? a[0] : 1);
        case "LEN": return toStr(a[0]).length;
        case "LEFT": return toStr(a[0]).slice(0, a[1]);
        case "RIGHT": return toStr(a[0]).slice(-a[1]);
        case "MID": return toStr(a[0]).substr(a[1] - 1, a.length > 2 ? a[2] : undefined);
        case "STR": return toStr(a[0]);
        case "VAL": return parseFloat(a[0]) || 0;
        case "CHR": return String.fromCharCode(a[0]);
        case "ASC": return toStr(a[0]).charCodeAt(0) || 0;
        case "UCASE": return toStr(a[0]).toUpperCase();
        case "LCASE": return toStr(a[0]).toLowerCase();
        default: throw new Error("unknown function " + nm + "()");
      }
    }
    function truthy(v) { return typeof v === "string" ? v.length > 0 : v !== 0; }
    function eq(a, b) { return (typeof a === "string" || typeof b === "string") ? toStr(a) === toStr(b) : a === b; }
    function toStr(v) {
      if (typeof v === "string") return v;
      if (typeof v === "number") { if (Number.isInteger(v)) return String(v); return String(Math.round(v * 1e10) / 1e10); }
      return String(v);
    }
    function evalStr(s) { var e = new Expr(lex(s)); var v = e.parse(); return v; }

    // ---- pre-scan program into logical lines; record label positions ----
    var raw = String(source || "").split(/\r?\n/);
    var lines = [];
    var labels = Object.create(null);
    for (var li = 0; li < raw.length; li++) {
      var ln = raw[li].replace(/\t/g, "    ");
      var trimmed = ln.trim();
      // label:  (a name followed by a colon, alone on the line)
      var lm = trimmed.match(/^([A-Za-z_]\w*):\s*$/);
      if (lm) { labels[lm[1].toUpperCase()] = lines.length; continue; }
      lines.push(trimmed);
    }

    // ---- execute with a program counter and a control-flow stack ----
    var pc = 0, steps = 0;
    var stack = []; // {type:'for',var,limit,step,pc} | {type:'while',pc}
    function findMatch(fromPc, openWords, closeWord) {
      var depth = 0;
      for (var k = fromPc + 1; k < lines.length; k++) {
        var w = firstWord(lines[k]);
        if (openWords.indexOf(w) >= 0) depth++;
        else if (w === closeWord) { if (depth === 0) return k; depth--; }
      }
      return -1;
    }
    function firstWord(l) { var m = l.match(/^([A-Za-z]+)/); return m ? m[1].toUpperCase() : ""; }

    while (pc < lines.length) {
      if (++steps > MAX_STEPS) { emit("\n[stopped: too many steps — possible infinite loop]\n"); break; }
      var line = lines[pc];
      if (!line) { pc++; continue; }
      var kw = firstWord(line);
      var rest = line.replace(/^[A-Za-z]+\s*/, "");

      if (kw === "REM" || line[0] === "'") { pc++; continue; }
      else if (kw === "PRINT" || line[0] === "?") {
        doPrint(line[0] === "?" ? line.slice(1) : rest); pc++;
      }
      else if (kw === "LET") { doAssign(rest); pc++; }
      else if (kw === "INPUT") { doInput(rest); pc++; }
      else if (kw === "IF") { pc = doIf(line, pc); }
      else if (kw === "ELSE" || kw === "ELSEIF") {
        // reached only when falling out of a taken THEN block: skip to ENDIF
        var e = findMatch(pc - 1 < 0 ? pc : findIfStart(pc), ["IF"], "ENDIF");
        pc = skipToEndif(pc); pc++;
      }
      else if (kw === "ENDIF") { pc++; }
      else if (kw === "FOR") { pc = doFor(rest, pc); }
      else if (kw === "NEXT") { pc = doNext(rest, pc); }
      else if (kw === "WHILE") { pc = doWhile(rest, pc); }
      else if (kw === "WEND") { pc = doWend(pc); }
      else if (kw === "GOTO") {
        var tgt = rest.trim().toUpperCase();
        if (!(tgt in labels)) { emit("\n[error: unknown label '" + rest.trim() + "']\n"); break; }
        pc = labels[tgt];
      }
      else if (kw === "END" || kw === "STOP") { break; }
      else if (/^[A-Za-z_]\w*\s*=/.test(line)) { doAssign(line); pc++; }
      else { emit("\n[error line " + (pc + 1) + ": don't understand '" + line + "']\n"); break; }
    }

    // ----- statement helpers -----
    function doPrint(args) {
      var s = args.trim();
      if (s === "") { emit("\n"); return; }
      var trailing = /[;,]\s*$/.test(s);
      var parts = splitTop(s, [";", ","]);
      var buf = "";
      for (var i = 0; i < parts.length; i++) {
        var seg = parts[i].expr.trim();
        if (seg !== "") buf += toStr(evalStr(seg));
        if (parts[i].sep === ",") buf += "\t";
      }
      emit(buf + (trailing ? "" : "\n"));
    }
    function doAssign(s) {
      var eq = s.indexOf("=");
      if (eq < 0) throw new Error("bad assignment");
      var name = s.slice(0, eq).trim().toUpperCase();
      var val = evalStr(s.slice(eq + 1));
      vars[name] = val;
    }
    function doInput(s) {
      var parts = s.split(",");
      var prompt = "";
      var startIdx = 0;
      var first = parts[0].trim();
      var pm = first.match(/^"([\s\S]*)"$/);
      // INPUT "prompt"; var    or   INPUT "prompt", var
      var semiSplit = s.split(";");
      var target, promptTxt = "";
      if (semiSplit.length > 1) { promptTxt = stripQuotes(semiSplit[0].trim()); target = semiSplit[1].trim(); }
      else { target = s.trim(); }
      if (promptTxt) emit(promptTxt);
      var v = inPos < inLines.length ? inLines[inPos++] : "";
      var name = target.toUpperCase();
      var num = parseFloat(v);
      vars[name] = (v !== "" && !isNaN(num) && /^\s*-?[0-9.]+\s*$/.test(v)) ? num : v;
      emit(v + "\n");
    }
    function stripQuotes(x) { var m = x.match(/^"([\s\S]*)"$/); return m ? m[1] : x; }

    function doIf(line, atPc) {
      // one-line:  IF cond THEN stmt [ELSE stmt]
      // block:     IF cond THEN <newline> ... [ELSEIF..] [ELSE ..] ENDIF
      var upper = line.toUpperCase();
      var thenIdx = findKeyword(line, "THEN");
      if (thenIdx < 0) throw new Error("IF without THEN");
      var cond = line.slice(2, thenIdx).trim();
      var after = line.slice(thenIdx + 4).trim();
      var condVal = truthy(evalStr(cond));
      if (after !== "") {
        // one-line IF
        var elseIdx = findKeyword(after, "ELSE");
        var thenStmt = elseIdx >= 0 ? after.slice(0, elseIdx).trim() : after;
        var elseStmt = elseIdx >= 0 ? after.slice(elseIdx + 4).trim() : "";
        var toRun = condVal ? thenStmt : elseStmt;
        if (toRun) { var j = runInline(toRun); if (j !== null && j !== undefined) return j; }
        return atPc + 1;
      }
      // block IF
      if (condVal) return atPc + 1; // enter THEN body; ELSE/ELSEIF handling will skip to ENDIF
      // jump to matching ELSEIF/ELSE/ENDIF
      var t = branchTargets(atPc);
      for (var i = 0; i < t.elifs.length; i++) {
        var cl = lines[t.elifs[i]];
        var ci = findKeyword(cl, "THEN");
        var cx = cl.slice(cl.toUpperCase().indexOf("ELSEIF") + 6, ci).trim();
        if (truthy(evalStr(cx))) return t.elifs[i] + 1;
      }
      if (t.elsePc >= 0) return t.elsePc + 1;
      return t.endifPc; // land on ENDIF (handled as no-op)
    }
    function branchTargets(ifPc) {
      var depth = 0, elifs = [], elsePc = -1, endifPc = -1;
      for (var k = ifPc + 1; k < lines.length; k++) {
        var w = firstWord(lines[k]);
        var hasThen = findKeyword(lines[k], "THEN") >= 0;
        if (w === "IF" && hasThen && !isOneLineIf(lines[k])) depth++;
        else if (w === "ENDIF") { if (depth === 0) { endifPc = k; break; } depth--; }
        else if (depth === 0 && w === "ELSEIF") elifs.push(k);
        else if (depth === 0 && w === "ELSE") elsePc = k;
      }
      return { elifs: elifs, elsePc: elsePc, endifPc: endifPc };
    }
    function isOneLineIf(l) {
      var ti = findKeyword(l, "THEN");
      return ti >= 0 && l.slice(ti + 4).trim() !== "";
    }
    function skipToEndif(atPc) {
      var depth = 0;
      for (var k = atPc + 1; k < lines.length; k++) {
        var w = firstWord(lines[k]);
        if (w === "IF" && !isOneLineIf(lines[k])) depth++;
        else if (w === "ENDIF") { if (depth === 0) return k; depth--; }
      }
      return lines.length;
    }
    function findIfStart(atPc) { return atPc; }

    // Runs a single statement inline (from a one-line IF). Returns a jump target
    // pc for control-flow statements (GOTO/END), or null to just advance normally.
    function runInline(stmt) {
      var w = firstWord(stmt);
      if (w === "PRINT" || stmt[0] === "?") { doPrint(stmt[0] === "?" ? stmt.slice(1) : stmt.replace(/^PRINT\s*/i, "")); return null; }
      if (w === "LET") { doAssign(stmt.replace(/^LET\s*/i, "")); return null; }
      if (w === "GOTO") { var tg = stmt.replace(/^GOTO\s*/i, "").trim().toUpperCase(); return (tg in labels) ? labels[tg] : null; }
      if (w === "END" || w === "STOP") return lines.length;
      if (/^[A-Za-z_]\w*\s*=/.test(stmt)) { doAssign(stmt); return null; }
      return null;
    }

    function doFor(rest, atPc) {
      // i = a TO b [STEP s]
      var eqi = rest.indexOf("=");
      var name = rest.slice(0, eqi).trim().toUpperCase();
      var toIdx = findKeyword(rest, "TO");
      var stepIdx = findKeyword(rest, "STEP");
      var startV = evalStr(rest.slice(eqi + 1, toIdx));
      var limit = evalStr(stepIdx >= 0 ? rest.slice(toIdx + 2, stepIdx) : rest.slice(toIdx + 2));
      var step = stepIdx >= 0 ? evalStr(rest.slice(stepIdx + 4)) : 1;
      vars[name] = startV;
      if ((step >= 0 && startV > limit) || (step < 0 && startV < limit)) {
        // skip loop body entirely
        var nx = matchNext(atPc);
        return nx + 1;
      }
      stack.push({ type: "for", v: name, limit: limit, step: step, pc: atPc });
      return atPc + 1;
    }
    function matchNext(forPc) {
      var depth = 0;
      for (var k = forPc + 1; k < lines.length; k++) {
        var w = firstWord(lines[k]);
        if (w === "FOR") depth++;
        else if (w === "NEXT") { if (depth === 0) return k; depth--; }
      }
      return lines.length - 1;
    }
    function doNext(rest, atPc) {
      var fr = stack[stack.length - 1];
      if (!fr || fr.type !== "for") { emit("\n[error: NEXT without FOR]\n"); return lines.length; }
      vars[fr.v] = vars[fr.v] + fr.step;
      if ((fr.step >= 0 && vars[fr.v] <= fr.limit) || (fr.step < 0 && vars[fr.v] >= fr.limit)) {
        return fr.pc + 1; // loop back to body
      }
      stack.pop();
      return atPc + 1;
    }
    function doWhile(rest, atPc) {
      if (truthy(evalStr(rest))) { stack.push({ type: "while", pc: atPc }); return atPc + 1; }
      var we = matchWend(atPc);
      return we + 1;
    }
    function matchWend(wpc) {
      var depth = 0;
      for (var k = wpc + 1; k < lines.length; k++) {
        var w = firstWord(lines[k]);
        if (w === "WHILE") depth++;
        else if (w === "WEND") { if (depth === 0) return k; depth--; }
      }
      return lines.length - 1;
    }
    function doWend(atPc) {
      var fr = stack[stack.length - 1];
      if (!fr || fr.type !== "while") { emit("\n[error: WEND without WHILE]\n"); return lines.length; }
      var cond = lines[fr.pc].replace(/^WHILE\s*/i, "");
      if (truthy(evalStr(cond))) return fr.pc + 1;
      stack.pop();
      return atPc + 1;
    }

    // split PRINT args on top-level ; or , (respecting quotes and parens)
    function splitTop(s, seps) {
      var parts = [], cur = "", depth = 0, inStr = false, lastSep = "";
      for (var i = 0; i < s.length; i++) {
        var c = s[i];
        if (c === '"') inStr = !inStr;
        if (!inStr && c === "(") depth++;
        if (!inStr && c === ")") depth--;
        if (!inStr && depth === 0 && seps.indexOf(c) >= 0) { parts.push({ expr: cur, sep: c }); cur = ""; continue; }
        cur += c;
      }
      parts.push({ expr: cur, sep: "" });
      return parts;
    }
    // find a whole-word keyword outside of quotes
    function findKeyword(s, kw) {
      var up = s.toUpperCase(), inStr = false;
      for (var i = 0; i <= up.length - kw.length; i++) {
        var c = s[i];
        if (c === '"') inStr = !inStr;
        if (inStr) continue;
        if (up.substr(i, kw.length) === kw) {
          var before = i === 0 ? " " : s[i - 1];
          var after = s[i + kw.length] || " ";
          if (!/[A-Za-z0-9_]/.test(before) && !/[A-Za-z0-9_]/.test(after)) return i;
        }
      }
      return -1;
    }

    return { out: out.join("") };
  }

  global.PFBasic = { run: run };
})(typeof window !== "undefined" ? window : globalThis);
