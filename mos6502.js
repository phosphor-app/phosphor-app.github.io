/* PF6502 — a small MOS 6502 assembler + emulator that runs in the browser.
   Assembles a subset of 6502 assembly (labels, the common instructions and
   addressing modes, .byte/.word data, *=$addr / .org) and executes it on a
   simulated CPU with 64 KB of memory.

   I/O convention (from py65 / easy6502 style monitors):
     - store a byte to $F001  -> prints that character to the output
     - load a byte from $F004 -> reads the next byte from the stdin box (0 at EOF)

   PF6502.run(source, stdin) -> { out, regs:{A,X,Y,SP,PC}, flags:{N,V,B,D,I,Z,C}, steps }.
   Nothing real executes — it's a safe software CPU. */
(function (global) {
  var OUT = 0xF001, IN = 0xF004, STACK = 0x0100, MAX_STEPS = 2000000;

  var BRANCH = { BCC: "C0", BCS: "C1", BEQ: "Z1", BNE: "Z0", BMI: "N1", BPL: "N0", BVC: "V0", BVS: "V1" };
  var IMPLIED = {
    BRK: 1, RTS: 1, RTI: 1, NOP: 1, CLC: 1, SEC: 1, CLI: 1, SEI: 1, CLV: 1, CLD: 1, SED: 1,
    TAX: 1, TAY: 1, TXA: 1, TYA: 1, TSX: 1, TXS: 1, PHA: 1, PLA: 1, PHP: 1, PLP: 1,
    INX: 1, INY: 1, DEX: 1, DEY: 1
  };
  var KNOWN = {};
  ("LDA LDX LDY STA STX STY TAX TAY TXA TYA TSX TXS PHA PLA PHP PLP ADC SBC AND ORA EOR BIT " +
   "INC DEC INX DEX INY DEY ASL LSR ROL ROR CMP CPX CPY JMP JSR RTS RTI BRK NOP " +
   "CLC SEC CLI SEI CLV CLD SED BCC BCS BEQ BNE BMI BPL BVC BVS").split(" ")
    .forEach(function (m) { KNOWN[m] = 1; });

  function run(source, stdin) {
    var out = [];
    var mem = new Uint8Array(65536);
    var inBytes = strBytes(stdin || ""), inPos = 0;

    // ---------- parse into a line list ----------
    var raw = String(source || "").split(/\r?\n/);
    var lines = [];
    for (var i = 0; i < raw.length; i++) {
      var line = stripComment(raw[i]);
      // pull leading labels ("name:" possibly followed by an instruction)
      var lm;
      while ((lm = line.match(/^\s*([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.*)$/))) {
        lines.push({ label: lm[1], text: "", src: i + 1 });
        line = lm[2];
      }
      var t = line.trim();
      if (t !== "") lines.push({ label: null, text: t, src: i + 1 });
    }

    // ---------- pass 1: assign addresses, collect labels ----------
    var addr = 0x0600;
    var labels = Object.create(null);
    var items = [];            // instructions + data, with addresses
    function fail(msg, src) { throw new Error("line " + src + ": " + msg); }

    for (var p = 0; p < lines.length; p++) {
      var L = lines[p];
      if (L.label) { labels[L.label.toUpperCase()] = addr; }
      var text = L.text;
      if (text === "") continue;

      var org = text.match(/^(?:\*\s*=|\.org)\s*(.+)$/i);
      if (org) { addr = num(org[1].trim()) & 0xFFFF; continue; }

      var dm = text.match(/^\.?(byte|word|db|dw|dcb)\s+(.*)$/i);
      if (dm) {
        var kind = dm[1].toLowerCase();
        var parts = splitData(dm[2]);
        var bytes = [];
        for (var d = 0; d < parts.length; d++) {
          var it = parts[d].trim();
          var sm = it.match(/^"([\s\S]*)"$/);
          if (sm) { var bs = strBytes(sm[1]); for (var b = 0; b < bs.length; b++) bytes.push({ v: bs[b], word: false }); }
          else if (kind === "word" || kind === "dw") bytes.push({ v: it, word: true });
          else bytes.push({ v: it, word: false });
        }
        items.push({ type: "data", addr: addr, bytes: bytes, src: L.src });
        for (var q = 0; q < bytes.length; q++) addr += bytes[q].word ? 2 : 1;
        continue;
      }

      // instruction:  MNEMONIC [operand]
      var im = text.match(/^([A-Za-z]{3})\b\s*(.*)$/);
      if (!im) fail("can't parse '" + text + "'", L.src);
      var op = im[1].toUpperCase(), rest = im[2].trim();
      if (!KNOWN[op]) fail("unknown instruction '" + op + "'", L.src);

      var mode, expr = null;
      if (BRANCH[op]) { mode = "rel"; expr = rest; }
      else if (IMPLIED[op] && rest === "") mode = "imp";
      else mode = parseMode(op, rest, function (m) { fail(m, L.src); });
      if (mode.expr !== undefined) { expr = mode.expr; mode = mode.mode; }

      var size = SIZE[mode];
      items.push({ type: "ins", op: op, mode: mode, expr: expr, addr: addr, size: size, src: L.src });
      addr += size;
    }

    // ---------- pass 2: resolve operands, lay data into memory ----------
    var addrToIndex = Object.create(null);
    var instrs = [];
    function resolve(expr) { return evalExpr(expr, labels); }

    for (var k = 0; k < items.length; k++) {
      var it2 = items[k];
      if (it2.type === "data") {
        var a = it2.addr;
        for (var e = 0; e < it2.bytes.length; e++) {
          var bd = it2.bytes[e];
          var vv = (typeof bd.v === "number") ? bd.v : resolve(bd.v);
          if (bd.word) { mem[a & 0xFFFF] = vv & 0xFF; mem[(a + 1) & 0xFFFF] = (vv >> 8) & 0xFF; a += 2; }
          else { mem[a & 0xFFFF] = vv & 0xFF; a += 1; }
        }
        continue;
      }
      var operand = null;
      if (it2.mode !== "imp" && it2.mode !== "acc") operand = resolve(it2.expr) & (it2.mode === "imm" ? 0xFF : 0xFFFF);
      addrToIndex[it2.addr] = instrs.length;
      instrs.push({ op: it2.op, mode: it2.mode, operand: operand, addr: it2.addr, size: it2.size, src: it2.src });
    }

    // ---------- execute ----------
    var A = 0, X = 0, Y = 0, SP = 0xFF;
    var C = 0, Z = 0, I = 0, D = 0, B = 0, V = 0, N = 0;
    var entry = labels["START"] !== undefined ? labels["START"]
              : labels["MAIN"] !== undefined ? labels["MAIN"]
              : (instrs.length ? instrs[0].addr : 0x0600);
    var PC = entry, steps = 0, halted = false;

    function rd(a2) {
      a2 &= 0xFFFF;
      if (a2 === IN) return inPos < inBytes.length ? inBytes[inPos++] : 0;
      return mem[a2];
    }
    function wr(a2, v) {
      a2 &= 0xFFFF; v &= 0xFF;
      if (a2 === OUT) { out.push(String.fromCharCode(v)); return; }
      mem[a2] = v;
    }
    function setNZ(v) { v &= 0xFF; Z = v === 0 ? 1 : 0; N = (v & 0x80) ? 1 : 0; }
    function push(v) { mem[STACK + SP] = v & 0xFF; SP = (SP - 1) & 0xFF; }
    function pull() { SP = (SP + 1) & 0xFF; return mem[STACK + SP]; }
    function getP() { return C | (Z << 1) | (I << 2) | (D << 3) | (B << 4) | (1 << 5) | (V << 6) | (N << 7); }
    function setP(v) { C = v & 1; Z = (v >> 1) & 1; I = (v >> 2) & 1; D = (v >> 3) & 1; B = (v >> 4) & 1; V = (v >> 6) & 1; N = (v >> 7) & 1; }

    function eaddr(ins) {
      switch (ins.mode) {
        case "zp": case "abs": return ins.operand;
        case "zpx": return (ins.operand + X) & 0xFF;
        case "zpy": return (ins.operand + Y) & 0xFF;
        case "absx": return (ins.operand + X) & 0xFFFF;
        case "absy": return (ins.operand + Y) & 0xFFFF;
        case "indx": { var pt = (ins.operand + X) & 0xFF; return mem[pt] | (mem[(pt + 1) & 0xFF] << 8); }
        case "indy": { var base = mem[ins.operand & 0xFF] | (mem[(ins.operand + 1) & 0xFF] << 8); return (base + Y) & 0xFFFF; }
        case "ind": return mem[ins.operand & 0xFFFF] | (mem[(ins.operand + 1) & 0xFFFF] << 8);
      }
      return ins.operand;
    }
    function operVal(ins) { return ins.mode === "imm" ? ins.operand : rd(eaddr(ins)); }

    while (!halted) {
      var idx = addrToIndex[PC];
      if (idx === undefined) break;               // ran off into data / end
      if (++steps > MAX_STEPS) { out.push("\n[stopped: instruction limit reached — possible infinite loop]\n"); break; }
      var ins = instrs[idx];
      var next = ins.addr + ins.size;
      var m, t;
      switch (ins.op) {
        case "LDA": A = operVal(ins); setNZ(A); break;
        case "LDX": X = operVal(ins); setNZ(X); break;
        case "LDY": Y = operVal(ins); setNZ(Y); break;
        case "STA": wr(eaddr(ins), A); break;
        case "STX": wr(eaddr(ins), X); break;
        case "STY": wr(eaddr(ins), Y); break;
        case "TAX": X = A; setNZ(X); break;
        case "TAY": Y = A; setNZ(Y); break;
        case "TXA": A = X; setNZ(A); break;
        case "TYA": A = Y; setNZ(A); break;
        case "TSX": X = SP; setNZ(X); break;
        case "TXS": SP = X; break;
        case "PHA": push(A); break;
        case "PLA": A = pull(); setNZ(A); break;
        case "PHP": push(getP() | 0x10); break;
        case "PLP": setP(pull()); break;
        case "AND": A &= operVal(ins); setNZ(A); break;
        case "ORA": A |= operVal(ins); setNZ(A); break;
        case "EOR": A ^= operVal(ins); setNZ(A); break;
        case "BIT": { m = operVal(ins); Z = (A & m) === 0 ? 1 : 0; N = (m & 0x80) ? 1 : 0; V = (m & 0x40) ? 1 : 0; break; }
        case "ADC": { m = operVal(ins); t = A + m + C; V = (~(A ^ m) & (A ^ t) & 0x80) ? 1 : 0; C = t > 0xFF ? 1 : 0; A = t & 0xFF; setNZ(A); break; }
        case "SBC": { m = operVal(ins) ^ 0xFF; t = A + m + C; V = (~(A ^ m) & (A ^ t) & 0x80) ? 1 : 0; C = t > 0xFF ? 1 : 0; A = t & 0xFF; setNZ(A); break; }
        case "CMP": { m = operVal(ins); t = A - m; C = A >= m ? 1 : 0; setNZ(t & 0xFF); break; }
        case "CPX": { m = operVal(ins); t = X - m; C = X >= m ? 1 : 0; setNZ(t & 0xFF); break; }
        case "CPY": { m = operVal(ins); t = Y - m; C = Y >= m ? 1 : 0; setNZ(t & 0xFF); break; }
        case "INC": { var ai = eaddr(ins); t = (rd(ai) + 1) & 0xFF; wr(ai, t); setNZ(t); break; }
        case "DEC": { var ad = eaddr(ins); t = (rd(ad) - 1) & 0xFF; wr(ad, t); setNZ(t); break; }
        case "INX": X = (X + 1) & 0xFF; setNZ(X); break;
        case "DEX": X = (X - 1) & 0xFF; setNZ(X); break;
        case "INY": Y = (Y + 1) & 0xFF; setNZ(Y); break;
        case "DEY": Y = (Y - 1) & 0xFF; setNZ(Y); break;
        case "ASL": { if (ins.mode === "acc") { C = (A >> 7) & 1; A = (A << 1) & 0xFF; setNZ(A); } else { var aa = eaddr(ins); m = rd(aa); C = (m >> 7) & 1; m = (m << 1) & 0xFF; wr(aa, m); setNZ(m); } break; }
        case "LSR": { if (ins.mode === "acc") { C = A & 1; A = A >> 1; setNZ(A); } else { var al = eaddr(ins); m = rd(al); C = m & 1; m = m >> 1; wr(al, m); setNZ(m); } break; }
        case "ROL": { var oc = C; if (ins.mode === "acc") { C = (A >> 7) & 1; A = ((A << 1) | oc) & 0xFF; setNZ(A); } else { var ar = eaddr(ins); m = rd(ar); C = (m >> 7) & 1; m = ((m << 1) | oc) & 0xFF; wr(ar, m); setNZ(m); } break; }
        case "ROR": { var oc2 = C; if (ins.mode === "acc") { C = A & 1; A = (A >> 1) | (oc2 << 7); setNZ(A); } else { var arr = eaddr(ins); m = rd(arr); C = m & 1; m = (m >> 1) | (oc2 << 7); wr(arr, m); setNZ(m); } break; }
        case "JMP": next = eaddr(ins); break;
        case "JSR": { var ret = (ins.addr + 3 - 1) & 0xFFFF; push((ret >> 8) & 0xFF); push(ret & 0xFF); next = ins.operand; break; }
        case "RTS": { var lo = pull(), hi = pull(); next = (((hi << 8) | lo) + 1) & 0xFFFF; break; }
        case "RTI": { setP(pull()); var l2 = pull(), h2 = pull(); next = ((h2 << 8) | l2) & 0xFFFF; break; }
        case "CLC": C = 0; break;  case "SEC": C = 1; break;
        case "CLI": I = 0; break;  case "SEI": I = 1; break;
        case "CLV": V = 0; break;
        case "CLD": D = 0; break;  case "SED": D = 1; break;
        case "NOP": break;
        case "BRK": halted = true; break;
        default:
          if (BRANCH[ins.op]) {
            var cond = BRANCH[ins.op], flag = cond[0], want = +cond[1];
            var cur = flag === "C" ? C : flag === "Z" ? Z : flag === "N" ? N : V;
            if (cur === want) next = ins.operand;
          }
      }
      PC = next & 0xFFFF;
    }

    return {
      out: out.join(""),
      regs: { A: A, X: X, Y: Y, SP: SP, PC: PC },
      flags: { N: N, V: V, B: B, D: D, I: I, Z: Z, C: C },
      steps: steps
    };
  }

  // ---------- helpers ----------
  var SIZE = { imp: 1, acc: 1, imm: 2, zp: 2, zpx: 2, zpy: 2, abs: 3, absx: 3, absy: 3, indx: 2, indy: 2, ind: 3, rel: 2 };

  function looksZP(expr) {
    var s = String(expr).trim();
    var m = s.match(/^\$([0-9a-fA-F]+)$/); if (m) return m[1].length <= 2;
    if (/^\d+$/.test(s)) return parseInt(s, 10) <= 0xFF;
    if (/^%[01]+$/.test(s)) return s.length - 1 <= 8;
    return false; // labels -> absolute
  }
  function parseMode(op, s, fail) {
    s = s.trim();
    if (s === "" || /^[Aa]$/.test(s)) return { mode: "acc" };
    if (s[0] === "#") return { mode: "imm", expr: s.slice(1).trim() };
    var m;
    if ((m = s.match(/^\(\s*([^,()]+)\s*,\s*[Xx]\s*\)$/))) return { mode: "indx", expr: m[1] };
    if ((m = s.match(/^\(\s*([^()]+)\s*\)\s*,\s*[Yy]$/))) return { mode: "indy", expr: m[1] };
    if ((m = s.match(/^\(\s*([^()]+)\s*\)$/))) return { mode: "ind", expr: m[1] };
    if ((m = s.match(/^(.+?)\s*,\s*[Xx]$/))) return { mode: looksZP(m[1]) ? "zpx" : "absx", expr: m[1] };
    if ((m = s.match(/^(.+?)\s*,\s*[Yy]$/))) return { mode: looksZP(m[1]) ? "zpy" : "absy", expr: m[1] };
    return { mode: looksZP(s) ? "zp" : "abs", expr: s };
  }
  function stripComment(line) {
    var out = "", inStr = false;
    for (var i = 0; i < line.length; i++) {
      var c = line[i];
      if (c === '"') inStr = !inStr;
      if (c === ";" && !inStr) break;
      out += c;
    }
    return out;
  }
  function splitData(s) {
    var parts = [], cur = "", inStr = false;
    for (var i = 0; i < s.length; i++) {
      var c = s[i];
      if (c === '"') inStr = !inStr;
      if (c === "," && !inStr) { parts.push(cur); cur = ""; continue; }
      cur += c;
    }
    if (cur.trim() !== "") parts.push(cur);
    return parts;
  }
  function strBytes(s) { var a = []; for (var i = 0; i < s.length; i++) a.push(s.charCodeAt(i) & 0xFF); return a; }
  function num(tok) {
    tok = tok.trim();
    if (tok[0] === "$") return parseInt(tok.slice(1), 16);
    if (tok[0] === "%") return parseInt(tok.slice(1), 2);
    return parseInt(tok, 10);
  }
  function term(tok, labels) {
    tok = tok.trim();
    if (tok[0] === "<") return evalExpr(tok.slice(1), labels) & 0xFF;
    if (tok[0] === ">") return (evalExpr(tok.slice(1), labels) >> 8) & 0xFF;
    if (tok[0] === "$") return parseInt(tok.slice(1), 16) | 0;
    if (tok[0] === "%") return parseInt(tok.slice(1), 2) | 0;
    if (/^\d+$/.test(tok)) return parseInt(tok, 10);
    var key = tok.toUpperCase();
    if (key in labels) return labels[key];
    throw new Error("unknown symbol '" + tok + "'");
  }
  function evalExpr(expr, labels) {
    expr = String(expr).trim();
    if (expr[0] === "<") return evalExpr(expr.slice(1), labels) & 0xFF;
    if (expr[0] === ">") return (evalExpr(expr.slice(1), labels) >> 8) & 0xFF;
    // split on + / - at top level (no parens in our expr grammar)
    var m = expr.match(/^([^+\-]+)([+\-].+)?$/);
    if (!m) throw new Error("bad expression '" + expr + "'");
    var v = term(m[1], labels);
    var rest = m[2] || "";
    var re = /([+\-])\s*([^+\-]+)/g, mm;
    while ((mm = re.exec(rest))) {
      var n = term(mm[2], labels);
      v = mm[1] === "+" ? v + n : v - n;
    }
    return v & 0xFFFF;
  }

  global.PF6502 = { run: run };
})(typeof window !== "undefined" ? window : globalThis);
