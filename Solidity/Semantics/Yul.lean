import Solidity.Semantics.Calls

/-!
# Inline assembly (level 1)

`assembly { … }` over the Yul idioms the common libraries use (OpenZeppelin's `StorageSlot`,
`Proxy`, `Address`, `ECDSA`, `Math`, `Create2`, `MessageHashUtils`, `Clones`, …), evaluated by the
function `yulExec`; the relation (`ExecStmt.assembly*`) and the interpreter both call it, so the
block contributes no proof cases of its own.

The spec has no byte-addressed memory: a Solidity memory value is a heap object.  A Yul value is
therefore a word, or a *pointer* `base + off` whose base is a heap object (a Solidity local of a
memory type read in the block, `mload(add(b, 32))`) or the free region the block got from
`mload(0x40)` (`YulBase.free`).  Block-local memory holds what the block wrote at concrete
addresses (the scratch space `[0, 0x40)`, the free-pointer slot, anything else) and in the free
region, byte by byte; a stored pointer is 32 pointer bytes and reads back as the pointer.  A read
of a byte the block did not write is stuck, except in the free-pointer slot (the pointer) and the
zero slot `[0x60, 0x80)`.  Words of a heap object are its length and elements / fields (a pointer
for a reference-typed element); a write stores the cleaned word at the element's type and may
shrink a length.  The block must leave Solidity's memory as it found it: at a normal exit a write
at a concrete address of `0x60` or above, or a free-pointer slot that does not hold a pointer into
the free region, is stuck (a block that reverts, returns or stops may clobber anything).

Words assigned to Solidity locals are cleaned to the local's type (`cleanWord`: masked,
sign-extended, high bytes of `bytesN`), the normalisation solc applies at the first use; a program
that observes the dirty bits in a later block is not covered.  `x.slot := s` points the local
storage pointer `x` at slot `s` (`absRef`, `Layout.lean`).  Not in the fragment (stuck): Yul
functions, loops, `leave`, `break`, `continue`; a pointer assigned to an integer local; calldata
pointers (`x.offset` / `x.length` of calldata locals); `msize`, `pc`, `codecopy`, `extcodecopy`,
`invalid`, `selfdestruct`; memory the block allocates and hands to Solidity as an object.
-/

namespace Solidity

open Ethereum (UInt256)

/-! ## Values and memory -/

/-- Base of a pointer: a heap object, or the free region `mload(0x40)` points at. -/
inductive YulBase where
  | obj (id : Nat)
  | free
  deriving DecidableEq, Repr, Inhabited

inductive YulVal where
  | word (w : Nat)
  | ptr (base : YulBase) (off : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A byte of block-local memory: a byte, or byte `i` of a stored pointer. -/
inductive YulCell where
  | byte (b : UInt8)
  | ptrByte (base : YulBase) (off : Nat) (i : Nat)
  deriving DecidableEq, Repr, Inhabited

structure YulMem where
  /-- Bytes written at concrete addresses. -/
  conc : Nat → Option YulCell := fun _ => none
  /-- Bytes written in the free region. -/
  free : Nat → Option YulCell := fun _ => none
  /-- A write at a concrete address of `0x60` or above (memory Solidity code may rely on). -/
  clobbered : Bool := false
  /-- A write into the free-pointer slot `[0x40, 0x60)`. -/
  fmpWritten : Bool := false
  /-- Return data of the last call the block made. -/
  rdata : Option ByteArray := none

structure YulState where
  fr : Frame
  m : Machine
  mem : YulMem := {}
  /-- Yul locals, innermost first. -/
  locals : List (Ident × YulVal) := []

/-- Outcome of a block: it fell through, reverted, or ended the message call (`return`, `stop`). -/
inductive YulOut where
  | done (st : YulState)
  | reverted (data : ByteArray)
  | halted (m : Machine) (data : ByteArray)

def W (n : Nat) : EVM.Word := .ofNat n

/-- A word, reduced. -/
def wn (n : Nat) : YulVal := .word (n % W256)

def ww (w : EVM.Word) : YulVal := .word w.toNat

def addrAdd : YulVal → Nat → YulVal
  | .word a, k => .word (a + k)
  | .ptr b o, k => .ptr b (o + k)

/-- Byte `i` (big-endian) of a stored value. -/
def cellOf : YulVal → Nat → YulCell
  | .word w, i => .byte ((w / 2 ^ (8 * (31 - i))) % 256).toUInt8
  | .ptr b o, i => .ptrByte b o i

/-- The value 32 consecutive cells hold: a word, or a pointer stored whole. -/
def assemble (cs : List YulCell) : Option YulVal :=
  match cs with
  | .ptrByte b o 0 :: _ => if cs = (List.range 32).map (.ptrByte b o) then some (.ptr b o) else none
  | _ => (cs.mapM fun (c : YulCell) => match c with | .byte x => some x | _ => none).map fun bs => .word (bytesToNatBE bs)

/-- The word of a value of an elementary type. -/
def scalarWord : Value → Option YulVal
  | .uint _ n => some (.word n)
  | .sint _ i => some (.word ((i % (W256 : Int)).toNat))
  | .literal i _ => if 0 ≤ i ∧ i < W256 then some (.word i.toNat) else none
  | .bool b => some (.word (if b then 1 else 0))
  | .address a => some (.word a.toNat)
  | .contract _ a => some (.word a.toNat)
  | .fixedBytes n bs => some (.word (bytesToNatBE bs * 2 ^ (8 * (31 - n.val))))
  | .strLit s => if s.size ≤ 32 then some (.word (bytesToNatBE s.toList * 2 ^ (8 * (32 - s.size)))) else none
  | .enum _ _ i => some (.word i)
  | _ => none

/-- The word of a Solidity value (a memory reference is a pointer to its object; a raw calldata
    word copied to memory, cleaned). -/
def valueToYul : Value → Option YulVal
  | .wrapped _ _ v => scalarWord v
  | .memRef id => some (.ptr (.obj id) 0)
  | .raw ty w true => (cleanWord ty w).bind scalarWord
  | v => scalarWord v

/-- The Solidity value of type `ty` a Yul value is stored as: a word cleaned to the type, a
    pointer to an object for a reference type. -/
def yulToValue (env : TypeEnv) (ty : Ty) : YulVal → Option Value
  | .word w =>
    match ty with
    | .user q n =>
      match env.enum? q n with
      | some e => if w < e.members.length then some (.enum q n w) else none
      | none =>
        match env.valueType? q n with
        | some t => (cleanWord t.underlying w).map (.wrapped q n)
        | none => if (env.contractKind? n).isSome then some (.contract n (EVM.address (w % 2 ^ 160))) else none
    | ty => cleanWord ty w
  | .ptr (.obj id) 0 =>
    match ty with
    | .bytes | .string | .dynArray _ | .array .. => some (.memRef id)
    | .user q n => if (env.struct? q n).isSome then some (.memRef id) else none
    | _ => none
  | _ => none

/-! ## Heap objects as words -/

/-- Word `i` of a heap object: a `bytes`/`string` is its length then its data (zero-padded; a word
    beyond the data is stuck); a dynamic array its length then its elements; a static array its
    elements; a struct its fields. -/
def objWord (o : HeapObj) (i : Nat) : Option YulVal :=
  match o with
  | .bytes _ data =>
    if i = 0 then some (.word data.size)
    else
      let start := (i - 1) * 32
      if start < data.size then
        some (.word (bytesToNatBE ((List.range 32).map fun k => if start + k < data.size then data.get! (start + k) else 0)))
      else none
  | .array _ elems fixed =>
    if fixed then elems[i]?.bind valueToYul
    else if i = 0 then some (.word elems.length) else elems[i - 1]?.bind valueToYul
  | .struct _ fields => (fields[i]?).bind fun f => valueToYul f.2

/-- Store word `i` of a heap object: a length may only shrink; an element or field takes the
    value of its type. -/
def objStoreWord (env : TypeEnv) (o : HeapObj) (i : Nat) (v : YulVal) : Option HeapObj :=
  match o with
  | .bytes s data =>
    match v with
    | .word w =>
      if i = 0 then if w ≤ data.size then some (.bytes s (data.extract 0 w)) else none
      else
        let start := (i - 1) * 32
        if start < data.size then
          let bs := natToBytesBE w 32
          some (.bytes s ⟨((List.range data.size).map fun k =>
            if start ≤ k ∧ k < start + 32 then bs[k - start]! else data.get! k).toArray⟩)
        else none
    | .ptr .. => none
  | .array e elems fixed =>
    if fixed then
      if i < elems.length then (yulToValue env e v).map fun x => .array e (elems.set i x) fixed else none
    else if i = 0 then
      match v with
      | .word n => if n ≤ elems.length then some (.array e (elems.take n) fixed) else none
      | .ptr .. => none
    else if i - 1 < elems.length then (yulToValue env e v).map fun x => .array e (elems.set (i - 1) x) fixed
    else none
  | .struct ty fields =>
    match ty with
    | .user q n => do
      let s ← env.struct? q n
      let (fty, _) ← s.fields[i]?
      let (fname, _) ← fields[i]?
      let x ← yulToValue env fty v
      pure (.struct ty (fields.set i (fname, x)))
    | _ => none

def objCell (h : Heap) (id k : Nat) : Option YulCell := do
  let o ← h.get? id
  let w ← objWord o (k / 32)
  pure (cellOf w (k % 32))

def objSetCell (env : TypeEnv) (h : Heap) (id k : Nat) (c : YulCell) : Option Heap := do
  let o ← h.get? id
  let i := k / 32
  let w ← objWord o i
  let w' ← assemble ((List.range 32).map fun j => if j = k % 32 then c else cellOf w j)
  let o' ← objStoreWord env o i w'
  pure (h.set id o')

/-! ## Memory access -/

/-- Memory the block did not write: the free pointer in its slot, zero in the zero slot. -/
def defaultConc (a : Nat) : Option YulCell :=
  if 0x40 ≤ a ∧ a < 0x60 then some (.ptrByte .free 0 (a - 0x40))
  else if 0x60 ≤ a ∧ a < 0x80 then some (.byte 0) else none

def readCell (st : YulState) : YulVal → Option YulCell
  | .word a => match st.mem.conc a with | some c => some c | none => defaultConc a
  | .ptr .free o => st.mem.free o
  | .ptr (.obj id) o => objCell st.m.heap id o

def writeCell (env : TypeEnv) (st : YulState) : YulVal → YulCell → Option YulState
  | .word a, c => some { st with mem := { st.mem with
      conc := fun x => if x = a then some c else st.mem.conc x,
      clobbered := st.mem.clobbered || decide (0x60 ≤ a),
      fmpWritten := st.mem.fmpWritten || decide (0x40 ≤ a ∧ a < 0x60) } }
  | .ptr .free o, c => some { st with mem := { st.mem with free := fun x => if x = o then some c else st.mem.free x } }
  | .ptr (.obj id) o, c => (objSetCell env st.m.heap id o c).map fun h => { st with m := { st.m with heap := h } }

def readCells (st : YulState) (a : YulVal) (n : Nat) : Option (List YulCell) :=
  (List.range n).mapM fun i => readCell st (addrAdd a i)

/-- `n` bytes from `a` (every one a byte the block can see). -/
def readBytes (st : YulState) (a : YulVal) (n : Nat) : Option ByteArray :=
  ((List.range n).mapM fun i => match readCell st (addrAdd a i) with | some (.byte b) => some b | _ => none).map
    fun (bs : List UInt8) => ⟨bs.toArray⟩

def writeCells (env : TypeEnv) (st : YulState) (a : YulVal) (cs : List YulCell) : Option YulState :=
  (cs.zipIdx).foldlM (fun st (c, i) => writeCell env st (addrAdd a i) c) st

def writeBytes (env : TypeEnv) (st : YulState) (a : YulVal) (bs : ByteArray) : Option YulState :=
  writeCells env st a (bs.toList.map .byte)

def loadWord (st : YulState) (a : YulVal) : Option YulVal :=
  match a with
  | .ptr (.obj id) o => if o % 32 = 0 then (st.m.heap.get? id).bind (objWord · (o / 32)) else (readCells st a 32).bind assemble
  | _ => (readCells st a 32).bind assemble

def storeWord (env : TypeEnv) (st : YulState) (a v : YulVal) : Option YulState :=
  match a with
  | .ptr (.obj id) o =>
    if o % 32 = 0 then do
      let ob ← st.m.heap.get? id
      let ob' ← objStoreWord env ob (o / 32) v
      pure { st with m := { st.m with heap := st.m.heap.set id ob' } }
    else writeCells env st a ((List.range 32).map (cellOf v))
  | _ => writeCells env st a ((List.range 32).map (cellOf v))

/-- Solidity's memory is as the block found it: no write at `0x60` or above, and the free-pointer
    slot, if written, holds a pointer into the free region (an allocation). -/
def exitOk (st : YulState) : Bool :=
  !st.mem.clobbered &&
    (!st.mem.fmpWritten || match (readCells st (.word 0x40) 32).bind assemble with
      | some (.ptr .free _) => true
      | _ => false)

/-- A block that wrote no block-local memory exits normally (the form a derivation meets after
    `simp`; unfolding `exitOk` would evaluate the free-pointer check). -/
@[simp] theorem exitOk_fresh (fr : Frame) (m : Machine) (ls : List (Ident × YulVal)) :
    exitOk { fr := fr, m := m, locals := ls } = true := rfl

/-! ## Names -/

def lookupLocal (st : YulState) (x : Ident) : Option YulVal := (st.locals.find? (·.1 == x)).map (·.2)

def setLocal (st : YulState) (x : Ident) (v : YulVal) : YulState :=
  { st with locals := go st.locals }
where
  go : List (Ident × YulVal) → List (Ident × YulVal)
    | [] => []
    | (y, w) :: rest => if y == x then (y, v) :: rest else (y, w) :: go rest

/-- The word of a constant: a literal, converted to the constant's type (solc admits no other
    constant in inline assembly). -/
def constWord (env : TypeEnv) (v : FlatVar) : Option YulVal :=
  match v.init with
  | some (.lit l) => do
    let lit ← literalValue l
    let (val, _) ← implicitConv env {} lit (env.canonTy v.declaredIn v.ty)
    valueToYul val
  | _ => none

/-- An identifier: a Yul local, a Solidity local (a memory reference as a pointer), a constant. -/
def yulIdent (fc : FlatContract) (st : YulState) (x : Ident) : Option YulVal :=
  match lookupLocal st x with
  | some v => some v
  | none =>
    match st.fr.get? x with
    | some l => match l.val with | .storageRef .. => none | v => valueToYul v
    | none =>
      match fc.varIn st.fr.here x with
      | some v => if v.mutability == .constant then constWord fc.types v else none
      | none => none

def slotOff (cfg : Config) (er : Solm.EvaledStorageRef) : Option (Nat × Nat) :=
  match cfg.storageLayout er with
  | some (.leaf loc) => some (loc.slot.toNat, loc.offset.val)
  | some (.anchor s) => some (s.toNat, 0)
  | _ => none

/-- `x.slot` / `x.offset` of a storage pointer or a state variable. -/
def yulSlotOff (cfg : Config) (fc : FlatContract) (st : YulState) (x : Ident) : Option (Nat × Nat) :=
  match st.fr.get? x with
  | some l => match l.val with | .storageRef er _ => slotOff cfg er | _ => none
  | none =>
    match fc.varIn st.fr.here x with
    | some v => if v.mutability == .mutable then slotOff cfg ⟨v.key, []⟩ else none
    | none => none

/-- `x := v`: a Yul local, or a Solidity local (cleaned to its type; not a storage pointer). -/
def yulAssign (env : TypeEnv) (st : YulState) (x : Ident) (v : YulVal) : Option YulState :=
  match lookupLocal st x with
  | some _ => some (setLocal st x v)
  | none =>
    match st.fr.get? x with
    | some l =>
      if l.loc == some .storage then none
      else (yulToValue env l.ty v).map fun val => { st with fr := st.fr.setVal x val }
    | none => none

/-! ## Builtins -/

/-- Arithmetic, comparison and bit operations; pointer arithmetic where it keeps the base. -/
def yulArith (f : YulBuiltin) (vs : List YulVal) : Option YulVal :=
  match f, vs with
  | .add, [.word a, .word b] => some (ww (W a + W b))
  | .add, [.ptr b o, .word k] | .add, [.word k, .ptr b o] => some (.ptr b (o + k))
  | .sub, [.word a, .word b] => some (ww (W a - W b))
  | .sub, [.ptr b o, .word k] => if k ≤ o then some (.ptr b (o - k)) else none
  | .sub, [.ptr b o, .ptr b' o'] => if b = b' then some (ww (W o - W o')) else none
  | .mul, [.word a, .word b] => some (ww (W a * W b))
  | .div, [.word a, .word b] => some (ww (UInt256.div (W a) (W b)))
  | .sdiv, [.word a, .word b] => some (ww (UInt256.sdiv (W a) (W b)))
  | .mod, [.word a, .word b] => some (ww (UInt256.mod (W a) (W b)))
  | .smod, [.word a, .word b] => some (ww (UInt256.smod (W a) (W b)))
  | .exp, [.word a, .word b] => some (ww (UInt256.exp (W a) (W b)))
  | .signextend, [.word b, .word x] => some (ww (UInt256.signextend (W b) (W x)))
  | .lt, [.word a, .word b] => some (ww (UInt256.lt (W a) (W b)))
  | .gt, [.word a, .word b] => some (ww (UInt256.gt (W a) (W b)))
  | .slt, [.word a, .word b] => some (ww (UInt256.slt (W a) (W b)))
  | .sgt, [.word a, .word b] => some (ww (UInt256.sgt (W a) (W b)))
  | .eq, [.word a, .word b] => some (ww (UInt256.eq (W a) (W b)))
  | .lt, [.ptr b o, .ptr b' o'] => if b = b' then some (.word (if o < o' then 1 else 0)) else none
  | .gt, [.ptr b o, .ptr b' o'] => if b = b' then some (.word (if o' < o then 1 else 0)) else none
  | .eq, [.ptr b o, .ptr b' o'] => if b = b' then some (.word (if o = o' then 1 else 0)) else none
  | .iszero, [.word a] => some (.word (if a = 0 then 1 else 0))
  | .iszero, [.ptr ..] => some (.word 0)
  | .and, [.word a, .word b] => some (ww (UInt256.land (W a) (W b)))
  | .or, [.word a, .word b] => some (ww (UInt256.lor (W a) (W b)))
  | .xor, [.word a, .word b] => some (ww (UInt256.xor (W a) (W b)))
  | .not, [.word a] => some (ww (UInt256.lnot (W a)))
  | .shl, [.word s, .word x] => some (ww (UInt256.shiftLeft (W x) (W s)))
  | .shr, [.word s, .word x] => some (ww (UInt256.shiftRight (W x) (W s)))
  | .sar, [.word s, .word x] => some (ww (UInt256.sar (W s) (W x)))
  | .byte, [.word n, .word x] => some (ww (UInt256.byteAt (W n) (W x)))
  | .addmod, [.word a, .word b, .word c] => some (ww (UInt256.addMod (W a) (W b) (W c)))
  | .mulmod, [.word a, .word b, .word c] => some (ww (UInt256.mulMod (W a) (W b) (W c)))
  | _, _ => none

def setEvm (st : YulState) (evm : EVM.State) : YulState := { st with m := { st.m with evm := evm } }

/-- The return value of a call and its return data, copied to `out`. -/
def finishCall (env : TypeEnv) (st : YulState) (z : Bool) (ret : ByteArray) (out : YulVal) (outsz : Nat) :
    Option (YulVal × YulState) := do
  let st1 := { st with mem := { st.mem with rdata := some ret } }
  let st2 ← writeBytes env st1 out (ret.extract 0 (min outsz ret.size))
  pure (.word (if z then 1 else 0), st2)

/-- `call` / `staticcall` / `delegatecall` with the gas request `gasReq` (`none`: `gas()`, all
    but one 64th) and the other arguments. -/
def yulCall (env : TypeEnv) (o : Oracle) (st : YulState) (f : YulBuiltin) (gasReq : Option Nat) (vs : List YulVal) :
    Option (YulVal × YulState) :=
  match f, vs with
  | .call, [.word a, .word v, inp, .word insz, out, .word outsz] => do
    let data ← readBytes st inp insz
    let (z, m', ret) := callViaEVMFn o st.m (EVM.address (a % 2 ^ 160)) v data st.m.evm.executionEnv.perm
      (calleeGas o st.m gasReq v)
    finishCall env { st with m := m' } z ret out outsz
  | .staticcall, [.word a, inp, .word insz, out, .word outsz] => do
    let data ← readBytes st inp insz
    let (z, m', ret) := callViaEVMFn o st.m (EVM.address (a % 2 ^ 160)) 0 data false (calleeGas o st.m gasReq 0)
    finishCall env { st with m := m' } z ret out outsz
  | .delegatecall, [.word a, inp, .word insz, out, .word outsz] => do
    let data ← readBytes st inp insz
    let (z, m', ret) := delegateCallViaEVMFn o st.m (EVM.address (a % 2 ^ 160)) data (calleeGas o st.m gasReq 0)
    finishCall env { st with m := m' } z ret out outsz
  | _, _ => none

/-- The value builtins that read the machine (and `gas()`, drawn from the oracle). -/
def yulEnv (o : Oracle) (st : YulState) (f : YulBuiltin) (vs : List YulVal) : Option (YulVal × YulState) :=
  let ee := st.m.evm.executionEnv
  match f, vs with
  | .caller, [] => some (wn ee.source.toNat, st)
  | .origin, [] => some (wn ee.sender.toNat, st)
  | .callvalue, [] => some (wn ee.weiValue.toNat, st)
  | .calldatasize, [] => some (wn ee.calldata.size, st)
  | .calldataload, [.word p] => some (.word (cdWord ee.calldata p), st)
  | .gasprice, [] => some (wn ee.gasPrice, st)
  | .gas, [] => some (wn (o.gasleft st.m.tick).toNat, { st with m := { st.m with tick := st.m.tick + 1 } })
  | .address, [] => some (wn st.m.this.toNat, st)
  | .balance, [.word a] => some (wn (balanceOf st.m.evm (EVM.address (a % 2 ^ 160))), st)
  | .selfbalance, [] => some (wn (balanceOf st.m.evm st.m.this), st)
  | .extcodesize, [.word a] => some (wn (codeSize st.m.evm (EVM.address (a % 2 ^ 160))), st)
  | .extcodehash, [.word a] => some (wn (st.m.evm.extCodeHash (W a)).2.toNat, st)
  | .chainid, [] => some (wn Ethereum.chainId, st)
  | .timestamp, [] => some (wn ee.header.timestamp, st)
  | .number, [] => some (wn ee.header.number, st)
  | .coinbase, [] => some (wn ee.header.beneficiary.toNat, st)
  | .gaslimit, [] => some (wn ee.header.gasLimit, st)
  | .basefee, [] => some (wn ee.header.baseFeePerGas, st)
  | .prevrandao, [] | .difficulty, [] => some (wn ee.header.prevRandao.toNat, st)
  | .blockhash, [.word n] => some (wn (st.m.evm.blockHash (W n)).toNat, st)
  | .returndatasize, [] => st.mem.rdata.map fun d => (wn d.size, st)
  | .sload, [.word k] => some (ww (Solm.EVM.storageLoad st.m.evm st.m.this (W k)), st)
  | .tload, [.word k] => some (ww (Solm.EVM.transientLoad st.m.evm st.m.this (W k)), st)
  | .mload, [p] => (loadWord st p).map (·, st)
  | .keccak256, [p, .word n] => (readBytes st p n).map fun bs => (wn (hashWord bs).toNat, st)
  | .create, [.word v, p, .word n] => do
    let code ← readBytes st p n
    let (addr, m', z, ret) := createViaEVMFn o st.m v code none
    pure (wn (if z then addr.toNat else 0), { st with m := m', mem := { st.mem with rdata := some (if z then .empty else ret) } })
  | .create2, [.word v, p, .word n, .word s] => do
    let code ← readBytes st p n
    let (addr, m', z, ret) := createViaEVMFn o st.m v code (some ⟨(natToBytesBE s 32).toArray⟩)
    pure (wn (if z then addr.toNat else 0), { st with m := m', mem := { st.mem with rdata := some (if z then .empty else ret) } })
  | _, _ => none

/-- A value builtin. -/
def yulValue (o : Oracle) (st : YulState) (f : YulBuiltin) (vs : List YulVal) : Option (YulVal × YulState) :=
  match yulArith f vs with
  | some v => some (v, st)
  | none => yulEnv o st f vs

/-! ## Evaluation -/

variable (cfg : Config) (o : Oracle) (fc : FlatContract)

mutual
/-- Evaluate an expression.  The arguments of a call are evaluated right to left; the gas
    argument `gas()` of a call is the request for all gas. -/
def yulEval (st : YulState) : YulExpr → Option (YulVal × YulState)
  | .lit w => some (.word w, st)
  | .ident x => (yulIdent fc st x).map (·, st)
  | .slot x => (yulSlotOff cfg fc st x).map fun p => (.word p.1, st)
  | .offset x => (yulSlotOff cfg fc st x).map fun p => (.word p.2, st)
  | .call f args =>
    if f = .call ∨ f = .staticcall ∨ f = .delegatecall then
      match args with
      | g :: rest => do
        let (vs, st1) ← yulEvalArgs st rest
        let (gasReq, st2) ← (match g with
          | .call .gas [] => some (none, st1)
          | g => (yulEval st1 g).bind fun p => match p.1 with | .word w => some (some w, p.2) | .ptr .. => none)
        yulCall fc.types o st2 f gasReq vs
      | [] => none
    else do
      let (vs, st1) ← yulEvalArgs st args
      yulValue o st1 f vs
def yulEvalArgs (st : YulState) : List YulExpr → Option (List YulVal × YulState)
  | [] => some ([], st)
  | e :: es => do
    let (vs, st1) ← yulEvalArgs st es
    let (v, st2) ← yulEval st1 e
    pure (v :: vs, st2)
end

def yulLog (st : YulState) (p : YulVal) (n : Nat) (ts : List Nat) : Option YulOut := do
  let data ← readBytes st p n
  pure (.done { st with m := st.m.pushLog { address := st.m.this, topics := (ts.map W).toArray, data := data } })

/-- A builtin called for its effect. -/
def yulEffect (st : YulState) : YulExpr → Option YulOut
  | .call f args => do
    let (vs, st1) ← yulEvalArgs cfg o fc st args
    match f, vs with
    | .revert, [p, .word n] => (readBytes st1 p n).map .reverted
    | .«return», [p, .word n] => (readBytes st1 p n).map (.halted st1.m)
    | .stop, [] => some (.halted st1.m .empty)
    | .mstore, [p, v] => (storeWord fc.types st1 p v).map .done
    | .mstore8, [p, .word v] => (writeCell fc.types st1 p (.byte (v % 256).toUInt8)).map .done
    | .sstore, [.word k, .word v] => some (.done (setEvm st1 (Solm.EVM.storageStore st1.m.evm st1.m.this (W k) (W v))))
    | .tstore, [.word k, .word v] => some (.done (setEvm st1 (Solm.EVM.transientStore st1.m.evm st1.m.this (W k) (W v))))
    | .calldatacopy, [dst, .word src, .word n] =>
      (writeBytes fc.types st1 dst (cdBytes st1.m.evm.executionEnv.calldata src n)).map .done
    | .returndatacopy, [dst, .word src, .word n] => do
      let rd ← st1.mem.rdata
      if src + n ≤ rd.size then (writeBytes fc.types st1 dst (rd.extract src (src + n))).map .done else none
    | .pop, [_] => some (.done st1)
    | .log0, [p, .word n] => yulLog st1 p n []
    | .log1, [p, .word n, .word t1] => yulLog st1 p n [t1]
    | .log2, [p, .word n, .word t1, .word t2] => yulLog st1 p n [t1, t2]
    | .log3, [p, .word n, .word t1, .word t2, .word t3] => yulLog st1 p n [t1, t2, t3]
    | .log4, [p, .word n, .word t1, .word t2, .word t3, .word t4] => yulLog st1 p n [t1, t2, t3, t4]
    | _, _ => none
  | _ => none

mutual
def yulExecStmt (st : YulState) : YulStmt → Option YulOut
  | .let x none => some (.done { st with locals := (x, .word 0) :: st.locals })
  | .let x (some e) => do
    let (v, st1) ← yulEval cfg o fc st e
    pure (.done { st1 with locals := (x, v) :: st1.locals })
  | .assign x e => do
    let (v, st1) ← yulEval cfg o fc st e
    let st2 ← yulAssign fc.types st1 x v
    pure (.done st2)
  | .assignSlot x e => do
    let (v, st1) ← yulEval cfg o fc st e
    let .word s := v | none
    let some l := st1.fr.get? x | none
    if l.loc != some .storage then none
    pure (.done { st1 with fr := st1.fr.setVal x (.storageRef (absRef l.ty s) l.ty) })
  | .expr e => yulEffect cfg o fc st e
  | .if c body => do
    let (v, st1) ← yulEval cfg o fc st c
    if v = .word 0 then pure (.done st1) else yulScoped st1 body
  | .switch e cases dflt => do
    let (v, st1) ← yulEval cfg o fc st e
    let .word w := v | none
    yulCases st1 w cases dflt
  | .block body => yulScoped st body
termination_by s => (sizeOf s, 0)
/-- A nested block: its `let`s end with it. -/
def yulScoped (st : YulState) (body : List YulStmt) : Option YulOut :=
  match yulExecStmts st body with
  | some (.done st') => some (.done { st' with locals := st'.locals.drop (st'.locals.length - st.locals.length) })
  | r => r
termination_by (sizeOf body, 1)
def yulExecStmts (st : YulState) : List YulStmt → Option YulOut
  | [] => some (.done st)
  | s :: ss => do
    match ← yulExecStmt st s with
    | .done st1 => yulExecStmts st1 ss
    | r => pure r
termination_by ss => (sizeOf ss, 0)
def yulCases (st : YulState) (w : Nat) : List (Nat × List YulStmt) → Option (List YulStmt) → Option YulOut
  | [], none => some (.done st)
  | [], some d => yulScoped st d
  | (v, body) :: rest, dflt => if v = w then yulScoped st body else yulCases st w rest dflt
termination_by cs dflt => (sizeOf cs + sizeOf dflt, 0)
end

/-- Run an `assembly { … }` block in frame `fr` and machine `m`: `none` when the block leaves the
    fragment or the spec cannot tell what it does (see the header). -/
def yulExec (fr : Frame) (m : Machine) (body : List YulStmt) : Option YulOut :=
  match yulExecStmts cfg o fc { fr := fr, m := m } body with
  | some (.done st) => if exitOk st then some (.done st) else none
  | r => r

end Solidity
