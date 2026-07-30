/* PyForge x86-64 assembly emulator (NASM/Intel syntax, subset).
   Safe software CPU — nothing real executes. PFAsm.run(source, stdin) -> {out}.
   Supports: section .data/.bss/.text, labels, db/dw/dd/dq, resb/resw/resd/resq,
   equ ($ - label), and instructions mov/lea/add/sub/imul/inc/dec/and/or/xor/not/neg/
   shl/shr/sar/cmp/test/jmp+conditionals/push/pop/call/ret/syscall.
   Linux syscalls: 0 read (stdin box), 1 write (output), 60 exit. */
(function (global) {
  var MASK64 = (1n << 64n) - 1n;
  var MEM_SIZE = 1 << 20;                // 1 MB
  var DATA_BASE = 0x1000;
  var STACK_TOP = 0x80000;               // rsp starts here, grows down
  var MAX_STEPS = 3000000;

  var SUB = {}; // sub-register name -> {r, bits}
  var R64 = ["rax","rbx","rcx","rdx","rsi","rdi","rbp","rsp",
             "r8","r9","r10","r11","r12","r13","r14","r15"];
  var E32 = ["eax","ebx","ecx","edx","esi","edi","ebp","esp"];
  R64.forEach(function (r) { SUB[r] = { r: r, bits: 64 }; });
  E32.forEach(function (e, i) { SUB[e] = { r: R64[i], bits: 32 }; });
  ["r8","r9","r10","r11","r12","r13","r14","r15"].forEach(function (r) {
    SUB[r + "d"] = { r: r, bits: 32 };
  });
  var LOW16 = ["ax","bx","cx","dx","si","di","bp","sp"];
  LOW16.forEach(function (n, i) { SUB[n] = { r: R64[i], bits: 16 }; });
  var LOW8 = { al: "rax", bl: "rbx", cl: "rcx", dl: "rdx", sil: "rsi", dil: "rdi", bpl: "rbp", spl: "rsp" };
  Object.keys(LOW8).forEach(function (n) { SUB[n] = { r: LOW8[n], bits: 8 }; });

  function run(source, stdin) {
    var out = [];
    var mem = new Uint8Array(MEM_SIZE);
    var symbols = Object.create(null);   // name -> BigInt (address or equ value)
    var instrs = [];                     // {op, args:[..], line}
    var labels = Object.create(null);    // .text label -> instruction index
    var entry = null;
    var addr = DATA_BASE;
    var section = ".text";

    function err(msg, line) { out.push("\nerror" + (line ? " (line " + line + ")" : "") + ": " + msg + "\n"); }

    // ---- assemble ----
    var raw = source.split(/\r?\n/);
    try {
      for (var li = 0; li < raw.length; li++) {
        var line = stripComment(raw[li]).trim();
        if (!line) continue;

        // leading label(s):  name:  possibly followed by more
        var m;
        while ((m = line.match(/^([A-Za-z_.$][\w.$]*)\s*:\s*/))) {
          var lname = m[1];
          if (section === ".text") labels[lname] = instrs.length;
          else symbols[lname] = BigInt(addr);
          line = line.slice(m[0].length);
        }
        if (!line) continue;

        var parts = line.split(/\s+/);
        var head = parts[0].toLowerCase();

        if (head === "section" || head === "segment") { section = parts[1]; continue; }
        if (head === "global" || head === "_global") { entry = parts[1]; continue; }
        if (head === "default" || head === "bits" || head === "extern") continue;

        // NASM data label without a colon:  "name db ..."  /  "name resb ..."
        var DATADIR = { db: 1, dw: 1, dd: 1, dq: 1, resb: 1, resw: 1, resd: 1, resq: 1 };
        if (parts.length >= 2 && DATADIR[parts[1].toLowerCase()]) {
          symbols[parts[0]] = BigInt(addr);
          line = line.slice(parts[0].length).trim();
          parts = line.split(/\s+/);
          head = parts[0].toLowerCase();
        }

        // name equ expr
        if (parts[1] && parts[1].toLowerCase() === "equ") {
          symbols[parts[0]] = evalExpr(line.slice(line.indexOf("equ") + 3), symbols, BigInt(addr));
          continue;
        }

        if (head === "db" || head === "dw" || head === "dd" || head === "dq") {
          var sz = { db: 1, dw: 2, dd: 4, dq: 8 }[head];
          var vals = splitArgs(line.slice(parts[0].length));
          for (var v = 0; v < vals.length; v++) addr = emit(mem, addr, vals[v], sz, symbols, err, li + 1);
          continue;
        }
        if (head === "resb" || head === "resw" || head === "resd" || head === "resq") {
          var usz = { resb: 1, resw: 2, resd: 4, resq: 8 }[head];
          addr += Number(evalExpr(parts.slice(1).join(" "), symbols, BigInt(addr))) * usz;
          continue;
        }

        // instruction
        instrs.push({ op: head, args: splitArgs(line.slice(parts[0].length)), line: li + 1 });
      }
    } catch (e) {
      err("assemble failed: " + e.message);
      return { out: out.join("") };
    }

    // ---- execute ----
    var regs = Object.create(null);
    R64.forEach(function (r) { regs[r] = 0n; });
    regs.rsp = BigInt(STACK_TOP);
    var fl = { zf: false, sf: false, cf: false, of: false };
    var ip = labels[entry || "_start"];
    if (ip === undefined) ip = labels["main"];
    if (ip === undefined) { err("no _start (or global) entry label found"); return { out: out.join("") }; }

    var inBytes = strToBytes(stdin || "");
    var inPos = 0;
    var steps = 0, halted = false;

    function getReg(name) {
      var s = SUB[name]; if (!s) throw new Error("bad register " + name);
      var val = regs[s.r] & MASK64;
      if (s.bits === 64) return val;
      var mask = (1n << BigInt(s.bits)) - 1n;
      return val & mask;
    }
    function setReg(name, val) {
      var s = SUB[name]; if (!s) throw new Error("bad register " + name);
      val &= MASK64;
      if (s.bits === 64) { regs[s.r] = val; return; }
      if (s.bits === 32) { regs[s.r] = val & 0xffffffffn; return; } // zero-extend
      var mask = (1n << BigInt(s.bits)) - 1n;
      regs[s.r] = (regs[s.r] & ~mask) | (val & mask);
    }
    function loadMem(a, size) {
      var i = Number(a & MASK64), out = 0n;
      for (var k = 0; k < size; k++) out |= BigInt(mem[(i + k) % MEM_SIZE]) << BigInt(8 * k);
      return out;
    }
    function storeMem(a, size, val) {
      var i = Number(a & MASK64);
      for (var k = 0; k < size; k++) mem[(i + k) % MEM_SIZE] = Number((val >> BigInt(8 * k)) & 0xffn);
    }
    // effective address for [ ... ]
    function ea(expr) {
      expr = expr.trim().replace(/^\[/, "").replace(/\]$/, "");
      var total = 0n;
      var terms = expr.split("+");
      for (var t = 0; t < terms.length; t++) {
        var term = terms[t].trim();
        if (!term) continue;
        if (term.indexOf("*") >= 0) {
          var mm = term.split("*");
          total += getReg(mm[0].trim().toLowerCase()) * BigInt(parseInt(mm[1].trim(), 10) || 1);
        } else if (SUB[term.toLowerCase()]) {
          total += getReg(term.toLowerCase());
        } else if (term in symbols) {
          total += symbols[term];
        } else {
          total += evalExpr(term, symbols, 0n);
        }
      }
      return total & MASK64;
    }
    function opSize(a, b) {
      var s = /\b(byte|word|dword|qword)\b/i.exec((a || "") + " " + (b || ""));
      if (s) return { byte: 1, word: 2, dword: 4, qword: 8 }[s[1].toLowerCase()];
      var reg = SUB[(a || "").toLowerCase()] || SUB[(b || "").toLowerCase()];
      return reg ? reg.bits / 8 : 8;
    }
    function isMem(o) { return o.indexOf("[") >= 0; }
    function readOperand(o, size) {
      o = o.trim();
      var low = o.toLowerCase();
      if (SUB[low]) return getReg(low);
      if (isMem(o)) return loadMem(ea(o.replace(/\b(byte|word|dword|qword)\b/gi, "").trim()), size);
      return evalExpr(o, symbols, 0n);   // immediate / label
    }
    function writeOperand(o, size, val) {
      o = o.trim();
      var low = o.toLowerCase();
      if (SUB[low]) { setReg(low, val); return; }
      if (isMem(o)) { storeMem(ea(o.replace(/\b(byte|word|dword|qword)\b/gi, "").trim()), size, val); return; }
      throw new Error("cannot write to " + o);
    }
    function setFlagsSub(a, b, size) {
      var bits = BigInt(size * 8), m = (1n << bits) - 1n;
      var r = (a - b) & m;
      fl.zf = r === 0n;
      fl.sf = (r >> (bits - 1n)) === 1n;
      fl.cf = (a & m) < (b & m);
      var sa = (a >> (bits - 1n)) & 1n, sb = (b >> (bits - 1n)) & 1n, sr = (r >> (bits - 1n)) & 1n;
      fl.of = (sa !== sb) && (sa !== sr);
      return r;
    }
    function setFlagsLogic(r, size) {
      var bits = BigInt(size * 8), m = (1n << bits) - 1n;
      r &= m; fl.zf = r === 0n; fl.sf = (r >> (bits - 1n)) === 1n; fl.cf = false; fl.of = false;
    }

    try {
      while (!halted) {
        if (ip < 0 || ip >= instrs.length) break;
        if (++steps > MAX_STEPS) { err("instruction limit reached (" + MAX_STEPS + ") — possible infinite loop"); break; }
        var ins = instrs[ip];
        var op = ins.op, a = ins.args[0], b = ins.args[1];
        var sz = opSize(a, b);
        var next = ip + 1;

        switch (op) {
          case "mov": writeOperand(a, sz, readOperand(b, sz) & MASK64); break;
          case "lea": setReg(a.trim().toLowerCase(), ea(b.replace(/\b(byte|word|dword|qword)\b/gi, "").trim())); break;
          case "add": { var r = (readOperand(a, sz) + readOperand(b, sz)); setFlagsLogic(r, sz); writeOperand(a, sz, r & MASK64); break; }
          case "sub": { var r2 = setFlagsSub(readOperand(a, sz), readOperand(b, sz), sz); writeOperand(a, sz, r2); break; }
          case "imul": case "mul": {
            if (b === undefined) { // one-operand form: RDX:RAX = RAX * src
              var pr = ({ 1: ["ah", "al"], 2: ["dx", "ax"], 4: ["edx", "eax"], 8: ["rdx", "rax"] })[sz] || ["edx", "eax"];
              var prod = getReg(sz === 1 ? "al" : pr[1]) * readOperand(a, sz);
              var mb = BigInt(sz * 8), mm = (1n << mb) - 1n;
              setReg(pr[1], prod & mm);
              if (SUB[pr[0]]) setReg(pr[0], (prod >> mb) & mm);
            } else { writeOperand(a, sz, (readOperand(a, sz) * readOperand(b, sz)) & MASK64); }
            break;
          }
          case "div": case "idiv": {
            var divisor = readOperand(a, sz);
            if (divisor === 0n) { err("division by zero", ins.line); halted = true; break; }
            var pair = ({ 2: ["dx", "ax"], 4: ["edx", "eax"], 8: ["rdx", "rax"] })[sz] || ["edx", "eax"];
            var dbits = BigInt(sz * 8), dm = (1n << dbits) - 1n;
            var dividend = ((getReg(pair[0]) & dm) << dbits) | (getReg(pair[1]) & dm);
            var q, r;
            if (op === "idiv") {
              var full = 1n << (dbits * 2n);
              var sD = dividend >= (full >> 1n) ? dividend - full : dividend;
              var sV = divisor >= (1n << (dbits - 1n)) ? divisor - (1n << dbits) : divisor;
              q = sD / sV; r = sD % sV;
            } else { q = dividend / divisor; r = dividend % divisor; }
            setReg(pair[1], q & dm); setReg(pair[0], r & dm);
            break;
          }
          case "rdtsc": {
            // pseudo timestamp — a value that varies each run, for randomness
            setReg("eax", BigInt(Math.floor(Math.random() * 0x100000000)));
            setReg("edx", BigInt(Math.floor(Math.random() * 0x100000000)));
            break;
          }
          case "inc": { var r4 = (readOperand(a, sz) + 1n) & MASK64; fl.zf = r4 === 0n; writeOperand(a, sz, r4); break; }
          case "dec": { var r5 = (readOperand(a, sz) - 1n) & MASK64; fl.zf = r5 === 0n; writeOperand(a, sz, r5); break; }
          case "and": { var r6 = readOperand(a, sz) & readOperand(b, sz); setFlagsLogic(r6, sz); writeOperand(a, sz, r6); break; }
          case "or": { var r7 = readOperand(a, sz) | readOperand(b, sz); setFlagsLogic(r7, sz); writeOperand(a, sz, r7); break; }
          case "xor": { var r8v = readOperand(a, sz) ^ readOperand(b, sz); setFlagsLogic(r8v, sz); writeOperand(a, sz, r8v); break; }
          case "not": writeOperand(a, sz, (~readOperand(a, sz)) & MASK64); break;
          case "neg": writeOperand(a, sz, (-readOperand(a, sz)) & MASK64); break;
          case "shl": case "sal": { var r9 = (readOperand(a, sz) << readOperand(b, sz)) & MASK64; setFlagsLogic(r9, sz); writeOperand(a, sz, r9); break; }
          case "shr": { var ra = readOperand(a, sz) >> readOperand(b, sz); setFlagsLogic(ra, sz); writeOperand(a, sz, ra); break; }
          case "cmp": setFlagsSub(readOperand(a, sz), readOperand(b, sz), sz); break;
          case "test": setFlagsLogic(readOperand(a, sz) & readOperand(b, sz), sz); break;
          case "push": { regs.rsp = (regs.rsp - 8n) & MASK64; storeMem(regs.rsp, 8, readOperand(a, 8)); break; }
          case "pop": { writeOperand(a, 8, loadMem(regs.rsp, 8)); regs.rsp = (regs.rsp + 8n) & MASK64; break; }
          case "call": { regs.rsp = (regs.rsp - 8n) & MASK64; storeMem(regs.rsp, 8, BigInt(ip + 1)); next = target(a); break; }
          case "ret": { next = Number(loadMem(regs.rsp, 8)); regs.rsp = (regs.rsp + 8n) & MASK64; break; }
          case "jmp": next = target(a); break;
          case "nop": break;
          case "syscall": case "int": {
            var rax = regs.rax & MASK64;
            if (rax === 60n) { halted = true; }
            else if (rax === 1n) {
              var buf = Number(regs.rsi & MASK64), n = Number(regs.rdx & MASK64), s = "";
              for (var w = 0; w < n; w++) s += String.fromCharCode(mem[(buf + w) % MEM_SIZE]);
              out.push(s); regs.rax = BigInt(n);
            } else if (rax === 0n) {
              var dbuf = Number(regs.rsi & MASK64), dn = Number(regs.rdx & MASK64), got = 0;
              while (got < dn && inPos < inBytes.length) mem[(dbuf + got++) % MEM_SIZE] = inBytes[inPos++];
              if (got < dn && inPos >= inBytes.length) mem[(dbuf + got++) % MEM_SIZE] = 10; // newline on EOF
              regs.rax = BigInt(got);
            } else { err("unsupported syscall " + rax, ins.line); halted = true; }
            break;
          }
          default:
            if (op[0] === "j") { if (cond(op, fl)) next = target(a); }
            else { err("unknown instruction '" + op + "'", ins.line); halted = true; }
        }
        ip = next;
      }
    } catch (e) {
      err(e.message);
    }

    function target(name) {
      name = name.trim();
      if (labels[name] === undefined) throw new Error("unknown label '" + name + "'");
      return labels[name];
    }
    // Snapshot the final CPU state so the UI can render a register/flags panel.
    var regSnap = {};
    R64.forEach(function (r) { regSnap[r] = regs[r] & ((1n << 64n) - 1n); });
    return { out: out.join(""), regs: regSnap, flags: { ZF: fl.zf, SF: fl.sf, CF: fl.cf, OF: fl.of }, steps: steps };
  }

  // ---- helpers ----
  function cond(op, fl) {
    switch (op) {
      case "je": case "jz": return fl.zf;
      case "jne": case "jnz": return !fl.zf;
      case "js": return fl.sf;  case "jns": return !fl.sf;
      case "jc": case "jb": case "jnae": return fl.cf;
      case "jnc": case "jae": case "jnb": return !fl.cf;
      case "ja": case "jnbe": return !fl.cf && !fl.zf;
      case "jbe": case "jna": return fl.cf || fl.zf;
      case "jl": case "jnge": return fl.sf !== fl.of;
      case "jge": case "jnl": return fl.sf === fl.of;
      case "jg": case "jnle": return !fl.zf && (fl.sf === fl.of);
      case "jle": case "jng": return fl.zf || (fl.sf !== fl.of);
      default: return false;
    }
  }
  function stripComment(line) {
    var q = 0, out = "";
    for (var i = 0; i < line.length; i++) {
      var c = line[i];
      if (c === '"' || c === "'") { if (q === 0) q = c; else if (q === c) q = 0; out += c; }
      else if (c === ";" && q === 0) break;
      else out += c;
    }
    return out;
  }
  function splitArgs(s) {
    var res = [], cur = "", q = 0, depth = 0;
    for (var i = 0; i < s.length; i++) {
      var c = s[i];
      if (c === '"' || c === "'") { if (q === 0) q = c; else if (q === c) q = 0; cur += c; }
      else if (c === "[" && !q) { depth++; cur += c; }
      else if (c === "]" && !q) { depth--; cur += c; }
      else if (c === "," && !q && depth === 0) { res.push(cur.trim()); cur = ""; }
      else cur += c;
    }
    if (cur.trim()) res.push(cur.trim());
    return res;
  }
  function emit(mem, addr, token, size, symbols, err, line) {
    token = token.trim();
    if ((token[0] === '"' || token[0] === "'") && token[token.length - 1] === token[0]) {
      var str = token.slice(1, -1);
      for (var i = 0; i < str.length; i++) mem[addr++] = str.charCodeAt(i) & 0xff;
      return addr;
    }
    var val = evalExpr(token, symbols, BigInt(addr));
    for (var k = 0; k < size; k++) mem[addr++] = Number((val >> BigInt(8 * k)) & 0xffn);
    return addr;
  }
  // tiny expression evaluator: numbers, chars, labels, $, + and -
  function evalExpr(expr, symbols, dollar) {
    var toks = expr.match(/(\$|[A-Za-z_.][\w.]*|0[xX][0-9a-fA-F]+|\d+|'[^']'|"[^"]"|[+\-])/g) || [];
    var total = 0n, sign = 1n;
    for (var i = 0; i < toks.length; i++) {
      var t = toks[i];
      if (t === "+") { sign = 1n; continue; }
      if (t === "-") { sign = -1n; continue; }
      var v;
      if (t === "$") v = dollar;
      else if (/^0[xX]/.test(t)) v = BigInt(t);
      else if (/^\d+$/.test(t)) v = BigInt(t);
      else if (t[0] === "'" || t[0] === '"') v = BigInt(t.charCodeAt(1));
      else if (t in symbols) v = symbols[t];
      else v = 0n; // unknown label -> 0 (best effort)
      total += sign * v; sign = 1n;
    }
    return total & MASK64;
  }
  function strToBytes(s) {
    var b = [];
    for (var i = 0; i < s.length; i++) {
      var c = s.charCodeAt(i);
      if (c < 128) b.push(c);
      else { var e = unescape(encodeURIComponent(s[i])); for (var j = 0; j < e.length; j++) b.push(e.charCodeAt(j)); }
    }
    return b;
  }

  global.PFAsm = { run: run };
})(typeof window !== "undefined" ? window : globalThis);
