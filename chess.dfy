// =====================================================================
//  VERIFIED CHESS MOVE VALIDATOR AND MOVE GENERATOR (two-player chess)
// =====================================================================
//  Written in Dafny. A line starting with // is a comment: Dafny ignores it.
//
//  THE BIG IDEA
//  ------------
//  1. SPECIFICATION: we describe the rules of chess in the simplest,
//     most obviously-correct way, using logic ("for all", "there exists").
//     This code is never meant to be fast. It only says WHAT is legal.
//  2. IMPLEMENTATION: we write normal loop-based code that decides legality.
//  3. PROOF: Dafny's automatic prover checks that the implementation always
//     agrees with the specification, for EVERY possible position and move.
//
//  If this file shows no errors, the proofs went through.
//
//  READING ORDER
//  -------------
//   Part 1: data types          Part 5: move effects (Apply)
//   Part 2: small helpers       Part 6: the legality specification
//   Part 3: board geometry      Part 7: implementation, proved against it
//   Part 4: attack rules        Part 8: move generator + theorems + test
// =====================================================================


// =====================================================================
//  DAFNY SYNTAX CHEAT SHEET (everything this file uses)
// =====================================================================
//  datatype T = A | B(x: int)     a type with alternatives (enum + struct)
//  v.field                        read a field of a value
//  r.(f := v)                     a copy of r with field f replaced by v
//  seq<T>  |s|  s[i]  s[a..b]     immutable list; its length; element i;
//                                 slice. s[..k] = first k elements.
//  s[i := v]                      copy of the list with element i set to v
//  function f(x: T): U { e }      pure calculation (just one expression)
//  predicate p(x: T) { e }        a function that returns true/false
//  ghost ...                      exists only for proofs; never executed
//  method m(x: T) returns (y: U)  ordinary code: variables, loops, return
//  requires P                     PRECONDITION: callers must make P true
//  ensures Q                      POSTCONDITION: this code guarantees Q
//  invariant I                    a loop fact true on every pass of the test
//  lemma L(...) requires..ensures.. { }   a theorem: a fact proved once
//  assert P;                      check P right here (also guides the prover)
//  P ==> Q                        implication: "if P then Q"
//  P <==> Q                       "if and only if" (P and Q always agree)
//  forall x :: P(x)               for every x, P(x) holds
//  exists x :: P(x)               there is some x with P(x)
//  x in s                         membership: is x an element of list s
//  match v { case A => ... }      choose by which alternative v is
//  var x := e;     x := e;        declare a variable; assign to it
//  const NAME: T := e             a fixed named value
//  A && B    A || B    !A         and, or, not
//
//  HOW TO CHECK AND RUN THIS FILE
//    - VS Code + the "Dafny" extension: open the file; proofs run as you
//      type (a green bar or a red squiggle on each failing line).
//    - Command line:  dafny verify chess.dfy
//    - Run the test:  dafny run chess.dfy   (or add --target:py)
//
//  WHAT IS PROVED (checked by Dafny, nothing assumed)
//    * IsLegalImpl agrees with the specification Legal on every input.
//    * GenLegal returns EXACTLY the set of legal moves: nothing illegal
//      (soundness) and nothing missing (completeness).
//    * A legal move never leaves the mover's king in check.
//    * IsCheckmate / IsStalemate agree with their definitions.
//  WHAT IS NOT PROVED (be honest about this in any write-up)
//    * That the specification itself is the true rule book of chess. A
//      proof only shows the code matches the spec, so a mistake in the
//      spec would survive. This is why Main tests the code against the
//      published perft counts, which come from independent engines.
//    * The FEN parser, Perft and Main are test helpers, not proved.
//    * Not modeled: draw rules (50-move, repetition, insufficient
//      material), and the move counters. Positions are assumed to be
//      normal chess positions (one king per side, no pawns on rows 0/7).
//    * Speed: GenLegal tries all 64 x 64 x 5 candidates. That is simple
//      to prove but slow; a fast generator can be proved equal to it.
// =====================================================================


// =====================================================================
// PART 1: DATA TYPES
// =====================================================================
// A `datatype` is a type with a fixed list of alternatives. Each
// alternative is a "constructor", optionally carrying named fields.

// A color is exactly one of two things. No fields.
datatype Color = White | Black

// The six kinds of piece.
datatype Kind = Pawn | Knight | Bishop | Rook | Queen | King

// A piece has a color and a kind. Here the type and its only constructor
// share the name Piece. Fields are read with a dot: p.color, p.kind.
datatype Piece = Piece(color: Color, kind: Kind)

// A board cell is either Empty or occupied by a piece.
datatype Cell = Empty | Occ(piece: Piece)

// A generic "maybe a value" type. <T> means "for any type T".
// Option<Kind> is either None or Some(a kind).
datatype Option<T> = None | Some(value: T)

// A square: r is the row 0..7 (row 0 = rank 1, White's back rank),
// c is the column 0..7 (column 0 = file a). Plain ints, so the code
// below checks 0 <= r < 8 itself whenever it matters.
datatype Square = Sq(r: int, c: int)

// A move: source, destination, and an optional promotion piece.
// (`from` and `to` are avoided as names; they can clash with keywords.)
datatype Move = Move(src: Square, dst: Square, promo: Option<Kind>)

// Which castling moves are still allowed (not yet "spent").
datatype Rights = Rights(wk: bool, wq: bool, bk: bool, bq: bool)

// A full game position:
//   board: 64 cells, cell number r*8 + c  (a `seq` is an immutable list)
//   side:  whose turn it is
//   rights: castling rights
//   ep: the en passant target square (the square a pawn skipped over on
//       the previous move), or None
datatype State = State(board: seq<Cell>, side: Color, rights: Rights, ep: Option<Square>)


// =====================================================================
// PART 2: SMALL HELPERS
// =====================================================================
// `function` defines a pure calculation: no loops, no changing variables,
// just an expression. The type after the colon is the result type.

function Opp(c: Color): Color
{
  match c
  case White => Black
  case Black => White
}

function Abs(x: int): int { if x < 0 then -x else x }

// -1, 0 or 1 depending on the sign of x.
function Sign(x: int): int { if x < 0 then -1 else if x > 0 then 1 else 0 }

// Which way a pawn of this color moves along the rows.
function Forward(c: Color): int { if c == White then 1 else -1 }
function HomeRow(c: Color): int { if c == White then 0 else 7 }
function PawnStartRow(c: Color): int { if c == White then 1 else 6 }
function PromoRow(c: Color): int { if c == White then 7 else 0 }

// A `predicate` is a function that returns true or false.
predicate OnBoard(s: Square) { 0 <= s.r < 8 && 0 <= s.c < 8 }

// Convert between a square and its index 0..63 in the board list.
function Idx(s: Square): int { s.r * 8 + s.c }
function SqOf(i: int): Square { Sq(i / 8, i % 8) }

// Read a cell. This is "total": it never crashes. An off-board square or
// a wrong-sized list simply reads as Empty. Callers check OnBoard first
// whenever it matters. `|b|` means "the length of the list b".
function At(b: seq<Cell>, s: Square): Cell
{
  if |b| == 64 && OnBoard(s) then b[Idx(s)] else Empty
}

// Write a cell: returns a NEW list with one cell replaced (lists never
// change in place). `b[i := x]` means "b, but with element i set to x".
// The `ensures` clause is a promise (a "postcondition") about the result:
// the length never changes. Dafny proves it. The name `r` after the colon
// lets the promise talk about the result.
function Put(b: seq<Cell>, s: Square, c: Cell): (r: seq<Cell>)
  ensures |r| == |b|
{
  if |b| == 64 && OnBoard(s) then b[Idx(s) := c] else b
}


// =====================================================================
// PART 3: BOARD GEOMETRY
// =====================================================================

predicate KnightStep(a: Square, b: Square)
{
  (Abs(b.r - a.r) == 1 && Abs(b.c - a.c) == 2) ||
  (Abs(b.r - a.r) == 2 && Abs(b.c - a.c) == 1)
}

predicate KingStep(a: Square, b: Square)
{
  a != b && Abs(b.r - a.r) <= 1 && Abs(b.c - a.c) <= 1
}

// Same diagonal (rows and columns differ by the same amount).
predicate Diagonal(a: Square, b: Square)
{
  a != b && Abs(b.r - a.r) == Abs(b.c - a.c)
}

// Same row or same column.
predicate Straight(a: Square, b: Square)
{
  a != b && (a.r == b.r || a.c == b.c)
}

// For a straight or diagonal line, the number of steps from a to b.
function Steps(a: Square, b: Square): int
{
  if Abs(b.r - a.r) > Abs(b.c - a.c) then Abs(b.r - a.r) else Abs(b.c - a.c)
}

// SPEC: every square strictly between a and b is empty.
// `ghost` means "exists only for the proof; never run". Walking from a
// toward b, step k lands on (a.r + k*dr, a.c + k*dc). `forall k :: P ==> Q`
// reads: for every integer k, if P then Q.
ghost predicate PathClear(bd: seq<Cell>, a: Square, b: Square)
{
  forall k {:trigger At(bd, Sq(a.r + k * Sign(b.r - a.r), a.c + k * Sign(b.c - a.c)))} ::
    1 <= k < Steps(a, b) ==>
    At(bd, Sq(a.r + k * Sign(b.r - a.r), a.c + k * Sign(b.c - a.c))) == Empty
}


// =====================================================================
// PART 4: ATTACK RULES (needed for check and castling)
// =====================================================================

// Does piece p, standing on f, attack square t? (Ignores whose turn it is.)
ghost predicate PieceAttacks(bd: seq<Cell>, p: Piece, f: Square, t: Square)
{
  match p.kind
  case Pawn   => t.r - f.r == Forward(p.color) && Abs(t.c - f.c) == 1
  case Knight => KnightStep(f, t)
  case King   => KingStep(f, t)
  case Bishop => Diagonal(f, t) && PathClear(bd, f, t)
  case Rook   => Straight(f, t) && PathClear(bd, f, t)
  case Queen  => (Diagonal(f, t) || Straight(f, t)) && PathClear(bd, f, t)
}

// Does the square f hold a piece of color `by` that attacks t?
ghost predicate Attacks(bd: seq<Cell>, f: Square, t: Square, attacker: Color)
{
  match At(bd, f)
  case Empty => false
  case Occ(p) => p.color == attacker && f != t && PieceAttacks(bd, p, f, t)
}

// SPEC: square t is attacked by color `by` if SOME board square (index
// 0..63) holds an attacker. `exists i :: P` means "there is an i with P".
ghost predicate IsAttacked(bd: seq<Cell>, t: Square, attacker: Color)
{
  exists i :: 0 <= i < 64 && Attacks(bd, SqOf(i), t, attacker)
}

// SPEC: color c is in check if its king stands on a square that the
// opponent attacks.
ghost predicate InCheck(bd: seq<Cell>, c: Color)
{
  exists i :: 0 <= i < 64 &&
    At(bd, SqOf(i)) == Occ(Piece(c, King)) &&
    IsAttacked(bd, SqOf(i), Opp(c))
}


// =====================================================================
// PART 5: WHAT A MOVE DOES (Apply)
// =====================================================================

// Remove castling rights that a move touching square s destroys: a king
// or rook leaving home, or a rook being captured on its home square.
// `rt.(wk := false)` means "rt, but with field wk set to false".
function ClearRights(rt: Rights, s: Square): Rights
{
  if s == Sq(0, 4) then rt.(wk := false, wq := false)
  else if s == Sq(7, 4) then rt.(bk := false, bq := false)
  else if s == Sq(0, 7) then rt.(wk := false)
  else if s == Sq(0, 0) then rt.(wq := false)
  else if s == Sq(7, 7) then rt.(bk := false)
  else if s == Sq(7, 0) then rt.(bq := false)
  else rt
}

// The position after playing move m. It assumes m is legal; Part 6 says
// what legal means. `var x := e;` names an intermediate value.
function Apply(s: State, m: Move): State
{
  match At(s.board, m.src)
  case Empty => s
  case Occ(p) =>
    // En passant: a pawn moves diagonally onto an empty square. The
    // captured pawn is NOT on the destination; it is beside the mover.
    var isEp := p.kind == Pawn && m.src.c != m.dst.c && At(s.board, m.dst) == Empty;
    // Castling: the king moves two columns.
    var isCastle := p.kind == King && Abs(m.dst.c - m.src.c) == 2;
    // A promotion replaces the pawn by the chosen piece.
    var placed := match m.promo
                  case Some(k) => Occ(Piece(p.color, k))
                  case None => Occ(p);
    var b1 := Put(Put(s.board, m.src, Empty), m.dst, placed);
    var b2 := if isEp then Put(b1, Sq(m.src.r, m.dst.c), Empty) else b1;
    // Castling also moves the rook.
    var b3 :=
      if isCastle && m.dst.c == 6 then
        Put(Put(b2, Sq(m.src.r, 7), Empty), Sq(m.src.r, 5), Occ(Piece(p.color, Rook)))
      else if isCastle && m.dst.c == 2 then
        Put(Put(b2, Sq(m.src.r, 0), Empty), Sq(m.src.r, 3), Occ(Piece(p.color, Rook)))
      else b2;
    // A two-square pawn push creates an en passant target square.
    var newEp :=
      if p.kind == Pawn && Abs(m.dst.r - m.src.r) == 2
      then Some(Sq((m.src.r + m.dst.r) / 2, m.src.c))
      else None;
    State(b3, Opp(s.side),
          ClearRights(ClearRights(s.rights, m.src), m.dst), newEp)
}


// =====================================================================
// PART 6: THE LEGALITY SPECIFICATION (the rules of chess)
// =====================================================================

function KingsideRight(rt: Rights, c: Color): bool { if c == White then rt.wk else rt.bk }
function QueensideRight(rt: Rights, c: Color): bool { if c == White then rt.wq else rt.bq }

// The destination must not hold a piece of the mover's own color.
predicate LandingOk(s: State, m: Move)
{
  match At(s.board, m.dst)
  case Empty => true
  case Occ(q) => q.color != s.side
}

predicate IsEnemy(b: seq<Cell>, sq: Square, c: Color)
{
  match At(b, sq)
  case Empty => false
  case Occ(q) => q.color != c
}

// Promotion: reaching the last row REQUIRES choosing N, B, R or Q;
// anywhere else, no promotion piece may be given.
predicate PromoOk(c: Color, m: Move)
{
  if m.dst.r == PromoRow(c) then
    (match m.promo
     case Some(k) => k == Knight || k == Bishop || k == Rook || k == Queen
     case None => false)
  else m.promo == None
}

// Pawn rules: one step, two steps from the start row, diagonal capture,
// en passant. `||` means "or", `&&` means "and".
predicate PawnRule(s: State, c: Color, m: Move)
{
  var dr := m.dst.r - m.src.r;
  var dc := m.dst.c - m.src.c;
  var f := Forward(c);
  ((dr == f && dc == 0 && At(s.board, m.dst) == Empty)
   || (dr == 2 * f && dc == 0 && m.src.r == PawnStartRow(c)
       && At(s.board, Sq(m.src.r + f, m.src.c)) == Empty
       && At(s.board, m.dst) == Empty)
   || (dr == f && Abs(dc) == 1 && IsEnemy(s.board, m.dst, c))
   || (dr == f && Abs(dc) == 1 && At(s.board, m.dst) == Empty
       && s.ep == Some(m.dst)
       && At(s.board, Sq(m.src.r, m.dst.c)) == Occ(Piece(Opp(c), Pawn))))
  && PromoOk(c, m)
}

// Castling: king on its home square e, right still held, rook in place,
// squares between empty, and the king is not in check, does not pass
// through an attacked square, and does not land on one.
ghost predicate CastleOK(s: State, m: Move)
{
  var c := s.side;
  var r := HomeRow(c);
  var opp := Opp(c);
  m.src == Sq(r, 4) && At(s.board, m.src) == Occ(Piece(c, King)) && m.promo == None &&
  (
    (m.dst == Sq(r, 6) && KingsideRight(s.rights, c)
     && At(s.board, Sq(r, 7)) == Occ(Piece(c, Rook))
     && At(s.board, Sq(r, 5)) == Empty && At(s.board, Sq(r, 6)) == Empty
     && !IsAttacked(s.board, Sq(r, 4), opp)
     && !IsAttacked(s.board, Sq(r, 5), opp)
     && !IsAttacked(s.board, Sq(r, 6), opp))
    ||
    (m.dst == Sq(r, 2) && QueensideRight(s.rights, c)
     && At(s.board, Sq(r, 0)) == Occ(Piece(c, Rook))
     && At(s.board, Sq(r, 1)) == Empty && At(s.board, Sq(r, 2)) == Empty
     && At(s.board, Sq(r, 3)) == Empty
     && !IsAttacked(s.board, Sq(r, 4), opp)
     && !IsAttacked(s.board, Sq(r, 3), opp)
     && !IsAttacked(s.board, Sq(r, 2), opp))
  )
}

// The movement pattern of the piece p standing on m.src.
ghost predicate PieceRule(s: State, p: Piece, m: Move)
{
  match p.kind
  case Knight => KnightStep(m.src, m.dst) && m.promo == None
  case Bishop => Diagonal(m.src, m.dst) && PathClear(s.board, m.src, m.dst) && m.promo == None
  case Rook   => Straight(m.src, m.dst) && PathClear(s.board, m.src, m.dst) && m.promo == None
  case Queen  => (Diagonal(m.src, m.dst) || Straight(m.src, m.dst))
                 && PathClear(s.board, m.src, m.dst) && m.promo == None
  case King   => (KingStep(m.src, m.dst) && m.promo == None) || CastleOK(s, m)
  case Pawn   => PawnRule(s, p.color, m)
}

// "Pseudo-legal": obeys piece movement, ignoring whether our own king ends
// up in check.
ghost predicate PseudoLegal(s: State, m: Move)
{
  OnBoard(m.src) && OnBoard(m.dst) && m.src != m.dst &&
  match At(s.board, m.src)
  case Empty => false
  case Occ(p) => p.color == s.side && LandingOk(s, m) && PieceRule(s, p, m)
}

// THE DEFINITION OF A LEGAL MOVE: pseudo-legal, and afterward the mover's
// king is not in check.
ghost predicate Legal(s: State, m: Move)
{
  PseudoLegal(s, m) && !InCheck(Apply(s, m).board, s.side)
}


// =====================================================================
// PART 7: IMPLEMENTATION (loops), PROVED AGAINST THE SPECIFICATION
// =====================================================================
// A `method` is ordinary code: it has variables, loops, and `return`.
// `returns (ok: bool)` declares the output. `ensures` is the contract: a
// promise about the output that Dafny must PROVE for all inputs.
// A `while` loop needs `invariant`s: facts that are true every time the
// loop test is reached. Dafny cannot run the loop symbolically, so the
// invariants are the only things it knows about the loop afterward.

// Walks from a toward b and checks every square in between.
method PathClearImpl(bd: seq<Cell>, a: Square, b: Square) returns (ok: bool)
  ensures ok <==> PathClear(bd, a, b)
{
  var n := Steps(a, b);
  var k := 1;
  while k < n
    invariant 1 <= k
    invariant n <= 1 || k <= n
    invariant forall j {:trigger At(bd, Sq(a.r + j * Sign(b.r - a.r), a.c + j * Sign(b.c - a.c)))} ::
                1 <= j < k && j < n ==>
                At(bd, Sq(a.r + j * Sign(b.r - a.r), a.c + j * Sign(b.c - a.c))) == Empty
  {
    if At(bd, Sq(a.r + k * Sign(b.r - a.r), a.c + k * Sign(b.c - a.c))) != Empty {
      assert 1 <= k < Steps(a, b);
      assert At(bd, Sq(a.r + k * Sign(b.r - a.r), a.c + k * Sign(b.c - a.c))) != Empty;
      return false;
    }
    k := k + 1;
  }
  return true;
}

// Implementation of Attacks: look at the piece on f and test its rule.
method AttacksImpl(bd: seq<Cell>, f: Square, t: Square, attacker: Color) returns (ok: bool)
  ensures ok <==> Attacks(bd, f, t, attacker)
{
  match At(bd, f) {
    case Empty => return false;
    case Occ(p) =>
      if p.color != attacker || f == t { return false; }
      match p.kind {
        case Pawn   => return t.r - f.r == Forward(p.color) && Abs(t.c - f.c) == 1;
        case Knight => return KnightStep(f, t);
        case King   => return KingStep(f, t);
        case Bishop =>
          if !Diagonal(f, t) { return false; }
          var clear := PathClearImpl(bd, f, t);
          return clear;
        case Rook =>
          if !Straight(f, t) { return false; }
          var clear := PathClearImpl(bd, f, t);
          return clear;
        case Queen =>
          if !(Diagonal(f, t) || Straight(f, t)) { return false; }
          var clear := PathClearImpl(bd, f, t);
          return clear;
      }
  }
}

// Implementation of IsAttacked: try every square, stop at the first hit.
method IsAttackedImpl(bd: seq<Cell>, t: Square, attacker: Color) returns (ok: bool)
  ensures ok <==> IsAttacked(bd, t, attacker)
{
  var i := 0;
  while i < 64
    invariant 0 <= i <= 64
    // no square before i attacks t:
    invariant forall j :: 0 <= j < i ==> !Attacks(bd, SqOf(j), t, attacker)
  {
    var a := AttacksImpl(bd, SqOf(i), t, attacker);
    if a { return true; }
    i := i + 1;
  }
  return false;
}

// Implementation of InCheck: find the king(s), test whether attacked.
method InCheckImpl(bd: seq<Cell>, c: Color) returns (ok: bool)
  ensures ok <==> InCheck(bd, c)
{
  var i := 0;
  while i < 64
    invariant 0 <= i <= 64
    invariant forall j :: 0 <= j < i ==>
      !(At(bd, SqOf(j)) == Occ(Piece(c, King)) && IsAttacked(bd, SqOf(j), Opp(c)))
  {
    if At(bd, SqOf(i)) == Occ(Piece(c, King)) {
      var a := IsAttackedImpl(bd, SqOf(i), Opp(c));
      if a { return true; }
    }
    i := i + 1;
  }
  return false;
}

method CastleOKImpl(s: State, m: Move) returns (ok: bool)
  ensures ok <==> CastleOK(s, m)
{
  var c := s.side;
  var r := HomeRow(c);
  var opp := Opp(c);
  if !(m.src == Sq(r, 4) && At(s.board, m.src) == Occ(Piece(c, King)) && m.promo == None) {
    return false;
  }
  if m.dst == Sq(r, 6) {
    if !(KingsideRight(s.rights, c) && At(s.board, Sq(r, 7)) == Occ(Piece(c, Rook))
         && At(s.board, Sq(r, 5)) == Empty && At(s.board, Sq(r, 6)) == Empty) {
      return false;
    }
    var a4 := IsAttackedImpl(s.board, Sq(r, 4), opp);
    var a5 := IsAttackedImpl(s.board, Sq(r, 5), opp);
    var a6 := IsAttackedImpl(s.board, Sq(r, 6), opp);
    return !a4 && !a5 && !a6;
  } else if m.dst == Sq(r, 2) {
    if !(QueensideRight(s.rights, c) && At(s.board, Sq(r, 0)) == Occ(Piece(c, Rook))
         && At(s.board, Sq(r, 1)) == Empty && At(s.board, Sq(r, 2)) == Empty
         && At(s.board, Sq(r, 3)) == Empty) {
      return false;
    }
    var a4 := IsAttackedImpl(s.board, Sq(r, 4), opp);
    var a3 := IsAttackedImpl(s.board, Sq(r, 3), opp);
    var a2 := IsAttackedImpl(s.board, Sq(r, 2), opp);
    return !a4 && !a3 && !a2;
  } else {
    return false;
  }
}

method PieceRuleImpl(s: State, p: Piece, m: Move) returns (ok: bool)
  ensures ok <==> PieceRule(s, p, m)
{
  match p.kind {
    case Knight => return KnightStep(m.src, m.dst) && m.promo == None;
    case Bishop =>
      if !(Diagonal(m.src, m.dst) && m.promo == None) { return false; }
      var clear := PathClearImpl(s.board, m.src, m.dst);
      return clear;
    case Rook =>
      if !(Straight(m.src, m.dst) && m.promo == None) { return false; }
      var clear := PathClearImpl(s.board, m.src, m.dst);
      return clear;
    case Queen =>
      if !((Diagonal(m.src, m.dst) || Straight(m.src, m.dst)) && m.promo == None) { return false; }
      var clear := PathClearImpl(s.board, m.src, m.dst);
      return clear;
    case King =>
      if KingStep(m.src, m.dst) && m.promo == None { return true; }
      var castle := CastleOKImpl(s, m);
      return castle;
    case Pawn => return PawnRule(s, p.color, m);
  }
}

method IsPseudoLegalImpl(s: State, m: Move) returns (ok: bool)
  ensures ok <==> PseudoLegal(s, m)
{
  if !(OnBoard(m.src) && OnBoard(m.dst) && m.src != m.dst) { return false; }
  match At(s.board, m.src) {
    case Empty => return false;
    case Occ(p) =>
      if p.color != s.side || !LandingOk(s, m) { return false; }
      var rule := PieceRuleImpl(s, p, m);
      return rule;
  }
}

// THE VALIDATOR: is move m legal in position s?
// The postcondition says this loop-based code always agrees with the
// declarative specification Legal.
method IsLegalImpl(s: State, m: Move) returns (ok: bool)
  ensures ok <==> Legal(s, m)
{
  var pl := IsPseudoLegalImpl(s, m);
  if !pl { return false; }
  var after := Apply(s, m);
  var chk := InCheckImpl(after.board, s.side);
  return !chk;
}


// =====================================================================
// PART 8: MOVE GENERATOR, THEOREMS, AND A TEST
// =====================================================================

// The promotion choices a generated move can carry.
const PromoOpts: seq<Option<Kind>> :=
  [None, Some(Knight), Some(Bishop), Some(Rook), Some(Queen)]

// A `lemma` is a theorem: a fact proved once and usable afterward.
// Here: a legal move always has on-board squares and a promotion value
// from PromoOpts. This guarantees the generator below misses nothing.
lemma LegalIsCandidate(s: State, m: Move)
  requires Legal(s, m)
  ensures OnBoard(m.src) && OnBoard(m.dst)
  ensures m.promo in PromoOpts
{
  assert PseudoLegal(s, m);
  match At(s.board, m.src) {
    case Empty =>
    case Occ(p) =>
      assert PieceRule(s, p, m);
      match p.kind {
        case Pawn =>
          assert PromoOk(p.color, m);
        case Knight => assert m.promo == None;
        case Bishop => assert m.promo == None;
        case Rook => assert m.promo == None;
        case Queen => assert m.promo == None;
        case King =>
          if KingStep(m.src, m.dst) && m.promo == None {
          } else {
            assert CastleOK(s, m);
          }
      }
  }
}

lemma IdxOfSqOf(i: int)
  requires 0 <= i < 64
  ensures OnBoard(SqOf(i)) && Idx(SqOf(i)) == i
{}

lemma SqOfIdx(s: Square)
  requires OnBoard(s)
  ensures 0 <= Idx(s) < 64 && SqOf(Idx(s)) == s
{}

// THE GENERATOR: returns exactly the legal moves.
// Two promises: SOUNDNESS (everything returned is legal) and
// COMPLETENESS (every legal move is returned).
//
// To keep the proof small and fast, the generator is built in three
// layers, each with its own simple contract:
//   GenFromTo: all legal moves from square i to square j (5 promo options)
//   GenFrom:   all legal moves from square i (loops over j)
//   GenLegal:  all legal moves (loops over i)

method GenFromTo(s: State, i: int, j: int) returns (ms: seq<Move>)
  requires 0 <= i < 64 && 0 <= j < 64
  ensures forall m :: m in ms ==> Legal(s, m) && m.src == SqOf(i) && m.dst == SqOf(j)
  ensures forall m :: Legal(s, m) && m.src == SqOf(i) && m.dst == SqOf(j) ==> m in ms
{
  ms := [];
  var k := 0;
  while k < 5
    invariant 0 <= k <= 5
    invariant forall m :: m in ms ==> Legal(s, m) && m.src == SqOf(i) && m.dst == SqOf(j)
    // every legal move i->j whose promo is among the first k options is in ms:
    invariant forall m :: (Legal(s, m) && m.src == SqOf(i) && m.dst == SqOf(j)
                           && m.promo in PromoOpts[..k]) ==> m in ms
  {
    var cand := Move(SqOf(i), SqOf(j), PromoOpts[k]);
    var ok := IsLegalImpl(s, cand);
    if ok { ms := ms + [cand]; }
    // Taking one more option extends the prefix by exactly one element:
    assert PromoOpts[..k + 1] == PromoOpts[..k] + [PromoOpts[k]];
    k := k + 1;
  }
  // k == 5, so the prefix is the whole list. Every legal move has a promo
  // value from that list (LegalIsCandidate), so none was missed.
  assert PromoOpts[..5] == PromoOpts;
  forall m | Legal(s, m) && m.src == SqOf(i) && m.dst == SqOf(j)
    ensures m in ms
  {
    LegalIsCandidate(s, m);
  }
}

method GenFrom(s: State, i: int) returns (ms: seq<Move>)
  requires 0 <= i < 64
  ensures forall m :: m in ms ==> Legal(s, m) && m.src == SqOf(i)
  ensures forall m :: Legal(s, m) && m.src == SqOf(i) ==> m in ms
{
  ms := [];
  var j := 0;
  while j < 64
    invariant 0 <= j <= 64
    invariant forall m :: m in ms ==> Legal(s, m) && m.src == SqOf(i)
    // all legal moves from i to any destination index below j are in ms:
    invariant forall jj :: 0 <= jj < j ==>
      forall m :: Legal(s, m) && m.src == SqOf(i) && m.dst == SqOf(jj) ==> m in ms
  {
    var part := GenFromTo(s, i, j);
    ms := ms + part;
    j := j + 1;
  }
  // A legal move has an on-board destination, which equals SqOf(jj) for
  // some jj in 0..63 (lemma SqOfIdx); the invariant covers every such jj.
  forall m | Legal(s, m) && m.src == SqOf(i)
    ensures m in ms
  {
    LegalIsCandidate(s, m);
    SqOfIdx(m.dst);
  }
}

method GenLegal(s: State) returns (moves: seq<Move>)
  ensures forall m :: m in moves ==> Legal(s, m)
  ensures forall m :: Legal(s, m) ==> m in moves
{
  moves := [];
  var i := 0;
  while i < 64
    invariant 0 <= i <= 64
    invariant forall m :: m in moves ==> Legal(s, m)
    invariant forall ii :: 0 <= ii < i ==>
      forall m :: Legal(s, m) && m.src == SqOf(ii) ==> m in moves
  {
    var part := GenFrom(s, i);
    moves := moves + part;
    i := i + 1;
  }
  forall m | Legal(s, m)
    ensures m in moves
  {
    LegalIsCandidate(s, m);
    SqOfIdx(m.src);
  }
}

// CHECKMATE and STALEMATE: the side to move has no legal move, and is
// (checkmate) or is not (stalemate) in check. The postconditions restate
// the definitions in logic; Dafny proves the code matches them.
method IsCheckmate(s: State) returns (b: bool)
  ensures b <==> (InCheck(s.board, s.side) && forall m :: !Legal(s, m))
{
  var moves := GenLegal(s);
  var chk := InCheckImpl(s.board, s.side);
  if |moves| == 0 {
    // GenLegal is complete: any legal move would be in the (empty) list.
    assert forall m :: !Legal(s, m);
  } else {
    // GenLegal is sound: the first listed move is legal, so "no legal
    // move" is false.
    assert moves[0] in moves;
    assert Legal(s, moves[0]);
  }
  return chk && |moves| == 0;
}

method IsStalemate(s: State) returns (b: bool)
  ensures b <==> (!InCheck(s.board, s.side) && forall m :: !Legal(s, m))
{
  var moves := GenLegal(s);
  var chk := InCheckImpl(s.board, s.side);
  if |moves| == 0 {
    // GenLegal is complete: any legal move would be in the (empty) list.
    assert forall m :: !Legal(s, m);
  } else {
    // GenLegal is sound: the first listed move is legal, so "no legal
    // move" is false.
    assert moves[0] in moves;
    assert Legal(s, moves[0]);
  }
  return !chk && |moves| == 0;
}

// Headline theorem: a legal move never leaves the mover's own king in check.
lemma LegalNeverLeavesKingInCheck(s: State, m: Move)
  requires Legal(s, m)
  ensures !InCheck(Apply(s, m).board, s.side)
{}

// Playing a move never changes the board size.
lemma ApplyKeepsBoardSize(s: State, m: Move)
  ensures |Apply(s, m).board| == |s.board|
{}

// Playing a move passes the turn to the opponent.
lemma LegalMovePassesTurn(s: State, m: Move)
  requires Legal(s, m)
  ensures Apply(s, m).side == Opp(s.side)
{
  assert PseudoLegal(s, m);
}

// ---------------------------------------------------------------------
// RUNNABLE TEST (not part of the proofs)
// ---------------------------------------------------------------------
function BackKind(c: int): Kind
{
  if c == 0 || c == 7 then Rook
  else if c == 1 || c == 6 then Knight
  else if c == 2 || c == 5 then Bishop
  else if c == 3 then Queen
  else King
}

function StartCell(i: int): Cell
{
  var r := i / 8;
  var c := i % 8;
  if r == 0 then Occ(Piece(White, BackKind(c)))
  else if r == 1 then Occ(Piece(White, Pawn))
  else if r == 6 then Occ(Piece(Black, Pawn))
  else if r == 7 then Occ(Piece(Black, BackKind(c)))
  else Empty
}

function StartState(): State
{
  State(seq(64, i requires 0 <= i < 64 => StartCell(i)),
        White, Rights(true, true, true, true), None)
}

// Counts positions reachable in `depth` moves (perft). Not verified.
method Perft(s: State, depth: nat) returns (count: nat)
  decreases depth
{
  if depth == 0 { return 1; }
  var moves := GenLegal(s);
  if depth == 1 { return |moves|; }
  count := 0;
  var i := 0;
  while i < |moves|
    invariant 0 <= i <= |moves|
  {
    var n := Perft(Apply(s, moves[i]), depth - 1);
    count := count + n;
    i := i + 1;
  }
}

// ---------------------------------------------------------------------
// FEN PARSER (test helper, not proved). FEN is the standard text format
// for a position, e.g. "8/8/8/8/8/8/8/K6k w - - 0 1".
// ---------------------------------------------------------------------
function CharToCell(ch: char): Cell
{
  match ch
  case 'P' => Occ(Piece(White, Pawn))   case 'p' => Occ(Piece(Black, Pawn))
  case 'N' => Occ(Piece(White, Knight)) case 'n' => Occ(Piece(Black, Knight))
  case 'B' => Occ(Piece(White, Bishop)) case 'b' => Occ(Piece(Black, Bishop))
  case 'R' => Occ(Piece(White, Rook))   case 'r' => Occ(Piece(Black, Rook))
  case 'Q' => Occ(Piece(White, Queen))  case 'q' => Occ(Piece(Black, Queen))
  case 'K' => Occ(Piece(White, King))   case 'k' => Occ(Piece(Black, King))
  case _ => Empty
}

method ParseFen(fen: string) returns (s: State)
{
  var board: seq<Cell> := seq(64, i => Empty);
  var r := 7;
  var c := 0;
  var i := 0;
  // 1) piece placement, from the top row (row 7) down
  while i < |fen| && fen[i] != ' '
    invariant 0 <= i <= |fen|
    invariant |board| == 64
  {
    var ch := fen[i];
    if ch == '/' {
      r := r - 1;
      c := 0;
    } else if '1' <= ch <= '8' {
      c := c + (ch as int) - ('0' as int);
    } else {
      board := Put(board, Sq(r, c), CharToCell(ch));
      c := c + 1;
    }
    i := i + 1;
  }
  // 2) side to move
  i := i + 1;
  var side := if i < |fen| && fen[i] == 'b' then Black else White;
  i := i + 2;
  if i > |fen| { i := |fen|; }   // stay inside the string on malformed input
  // 3) castling rights
  var rights := Rights(false, false, false, false);
  while i < |fen| && fen[i] != ' '
    invariant 0 <= i <= |fen|
  {
    if fen[i] == 'K' { rights := rights.(wk := true); }
    else if fen[i] == 'Q' { rights := rights.(wq := true); }
    else if fen[i] == 'k' { rights := rights.(bk := true); }
    else if fen[i] == 'q' { rights := rights.(bq := true); }
    i := i + 1;
  }
  // 4) en passant square
  i := i + 1;
  var ep: Option<Square> := None;
  if i + 1 < |fen| && 'a' <= fen[i] <= 'h' {
    ep := Some(Sq((fen[i + 1] as int) - ('1' as int), (fen[i] as int) - ('a' as int)));
  }
  return State(board, side, rights, ep);
}

method PerftFen(name: string, fen: string, maxDepth: nat, expected: seq<nat>)
{
  var s := ParseFen(fen);
  var d := 1;
  while d <= maxDepth && d <= |expected|
    invariant 1 <= d
  {
    var n := Perft(s, d);
    print name, " depth ", d, ": ", n, "  (expected ", expected[d - 1], ")",
          if n == expected[d - 1] then "  OK\n" else "  MISMATCH\n";
    d := d + 1;
  }
}

method Main()
{
  // Standard perft test positions from the Chess Programming Wiki.
  PerftFen("start   ", "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", 2, [20, 400]);
  PerftFen("kiwipete", "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", 2, [48, 2039]);
  PerftFen("position3", "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", 3, [14, 191, 2812]);
  PerftFen("position4", "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1", 2, [6, 264]);
  PerftFen("position5", "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8", 2, [44, 1486]);

  // Checkmate and stalemate checks.
  var mated := ParseFen("rnb1kbnr/pppp1ppp/8/4p3/6Pq/5P2/PPPPP2P/RNBQKBNR w KQkq - 1 3");
  var m1 := IsCheckmate(mated);
  print "fool's mate, White to move, checkmate? ", m1, "  (expected true)\n";
  var stale := ParseFen("7k/5Q2/6K1/8/8/8/8/8 b - - 0 1");
  var m2 := IsStalemate(stale);
  print "queen+king vs king, Black to move, stalemate? ", m2, "  (expected true)\n";
  var m3 := IsCheckmate(StartState());
  print "start position, checkmate? ", m3, "  (expected false)\n";
}
