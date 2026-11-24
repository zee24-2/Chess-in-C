// verified chess move validator and move generator in dafny
//
// basic idea:
// 1. specification: describe chess rules in plain logic (for all / there exists).
//    not meant to be fast, just defines what a legal move actually is.
// 2. implementation: normal loop-based code that decides legality.
// 3. proof: dafny checks that the loop code matches the spec on every possible board.
//
// structure:
// part 1: datatypes              part 6: legality specification
// part 2: small helpers          part 7: loop implementation + proofs
// part 3: board geometry         part 8: move generator and theorems
// part 4: attack & check rules   part 9: draw rules, move counters, game status
// part 5: applying a move        part 10: perft and game tests (unverified)
//
// what is proved:
// - IsLegalImpl agrees with Legal on every input
// - GenLegal returns the exact set of legal moves (soundness + completeness)
// - a legal move never leaves your own king in check
// - IsCheckmate and IsStalemate match their formal definitions
// - Apply updates the halfmove clock, the fullmove number and the position
//   history exactly as the rules say (lemma ApplyUpdatesCounters)
// - GameStatus agrees with StatusSpec: checkmate, stalemate, fifty-move
//   draw, threefold repetition, or ongoing (in that order of priority)
//
// limitations (not proved):
// - if the spec itself had a rule mistake, the proof wouldn't catch it (tested via perft)
// - ParseFen, Perft, Play and Main are unverified test helpers
// - insufficient material is not modeled
// - the repetition key is (board, side to move, castling rights, en passant square),
//   the same simplification the C engine uses. FIDE only counts the en passant
//   square when a capture is actually possible, so in rare positions this key can
//   count a repetition slightly later than the official rules
// - the draw is automatic here; in official chess the fifty-move and threefold
//   draws are claimed by a player (the 75-move and fivefold rules are automatic)


// --- PART 1: DATA TYPES ---

datatype Color = White | Black

datatype Kind = Pawn | Knight | Bishop | Rook | Queen | King

datatype Piece = Piece(color: Color, kind: Kind)

// a cell is either empty or holds a piece
datatype Cell = Empty | Occ(piece: Piece)

// generic maybe type so promotion can be None or Some(piece)
datatype Option<T> = None | Some(value: T)

// r = row 0..7 (0 is rank 1 / white's back rank), c = col 0..7 (0 is file a)
datatype Square = Sq(r: int, c: int)

// avoiding 'from' and 'to' as field names since they clash with keywords
datatype Move = Move(src: Square, dst: Square, promo: Option<Kind>)

// castling rights: wk, wq, bk, bq
datatype Rights = Rights(wk: bool, wq: bool, bk: bool, bq: bool)

// the part of a position that matters for repetition: two positions with the
// same Key are "the same position". move counters and history are NOT part of it
datatype Key = Key(board: seq<Cell>, side: Color, rights: Rights, ep: Option<Square>)

// full game state:
// board is an immutable 64-element sequence indexed by r*8 + c
// halfmove: plies since the last pawn move or capture (the fifty-move clock)
// fullmove: the move number, starts at 1 and goes up after Black moves
// history: the Key of every position that has occurred in the game, in order,
//          INCLUDING the current position (same idea as history[] in the C code)
datatype State = State(board: seq<Cell>, side: Color, rights: Rights, ep: Option<Square>,
                       halfmove: int, fullmove: int, history: seq<Key>)

// the repetition key of a state
function KeyOf(s: State): Key
{
  Key(s.board, s.side, s.rights, s.ep)
}


// --- PART 2: SMALL HELPERS ---

function Opp(c: Color): Color
{
  match c
  case White => Black
  case Black => White
}

function Abs(x: int): int { if x < 0 then -x else x }

// returns -1, 0, or 1 depending on sign
function Sign(x: int): int { if x < 0 then -1 else if x > 0 then 1 else 0 }

// pawn direction and key ranks per color
function Forward(c: Color): int { if c == White then 1 else -1 }
function HomeRow(c: Color): int { if c == White then 0 else 7 }
function PawnStartRow(c: Color): int { if c == White then 1 else 6 }
function PromoRow(c: Color): int { if c == White then 7 else 0 }

// bounds check, same as IN(r, c) in the C code
predicate OnBoard(s: Square) { 0 <= s.r < 8 && 0 <= s.c < 8 }

// convert between Square(r, c) and flat index 0..63
function Idx(s: Square): int { s.r * 8 + s.c }
function SqOf(i: int): Square { Sq(i / 8, i % 8) }

// read a cell safely; off-board squares just return Empty so it never crashes
function At(b: seq<Cell>, s: Square): Cell
{
  if |b| == 64 && OnBoard(s) then b[Idx(s)] else Empty
}

// returns a brand new board sequence with square s updated (seqs are immutable)
function Put(b: seq<Cell>, s: Square, c: Cell): (r: seq<Cell>)
  ensures |r| == |b|
{
  if |b| == 64 && OnBoard(s) then b[Idx(s) := c] else b
}


// --- PART 3: BOARD GEOMETRY ---

predicate KnightStep(a: Square, b: Square)
{
  (Abs(b.r - a.r) == 1 && Abs(b.c - a.c) == 2) ||
  (Abs(b.r - a.r) == 2 && Abs(b.c - a.c) == 1)
}

predicate KingStep(a: Square, b: Square)
{
  a != b && Abs(b.r - a.r) <= 1 && Abs(b.c - a.c) <= 1
}

// same diagonal if row diff equals col diff
predicate Diagonal(a: Square, b: Square)
{
  a != b && Abs(b.r - a.r) == Abs(b.c - a.c)
}

// same rank or file
predicate Straight(a: Square, b: Square)
{
  a != b && (a.r == b.r || a.c == b.c)
}

// number of steps along a straight or diagonal line from a to b
function Steps(a: Square, b: Square): int
{
  if Abs(b.r - a.r) > Abs(b.c - a.c) then Abs(b.r - a.r) else Abs(b.c - a.c)
}

// spec: every intermediate square strictly between a and b must be empty
// ghost means this is only used for proofs and erased at runtime
ghost predicate PathClear(bd: seq<Cell>, a: Square, b: Square)
{
  forall k {:trigger At(bd, Sq(a.r + k * Sign(b.r - a.r), a.c + k * Sign(b.c - a.c)))} ::
    1 <= k < Steps(a, b) ==>
    At(bd, Sq(a.r + k * Sign(b.r - a.r), a.c + k * Sign(b.c - a.c))) == Empty
}


// --- PART 4: ATTACK AND CHECK RULES ---

// checks if piece p standing on f attacks square t
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

// checks if square f has a piece of color 'attacker' that hits t
ghost predicate Attacks(bd: seq<Cell>, f: Square, t: Square, attacker: Color)
{
  match At(bd, f)
  case Empty => false
  case Occ(p) => p.color == attacker && f != t && PieceAttacks(bd, p, f, t)
}

// spec: square t is attacked if there exists at least one square 0..63 attacking it
ghost predicate IsAttacked(bd: seq<Cell>, t: Square, attacker: Color)
{
  exists i :: 0 <= i < 64 && Attacks(bd, SqOf(i), t, attacker)
}

// point of InCheck is to see if color c's king is currently under attack
ghost predicate InCheck(bd: seq<Cell>, c: Color)
{
  exists i :: 0 <= i < 64 &&
    At(bd, SqOf(i)) == Occ(Piece(c, King)) &&
    IsAttacked(bd, SqOf(i), Opp(c))
}


// --- PART 5: MOVE EFFECTS (Apply) ---

// strip castling rights if a king or rook moves from or gets captured on its home square
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

// returns the new state after playing move m (handles en passant, castling, promotion)
// it also updates the three bookkeeping fields:
//   halfmove: reset to 0 on a pawn move or a capture, otherwise +1
//   fullmove: +1 after Black moves
//   history:  the old history with the Key of the new position added at the end
function Apply(s: State, m: Move): State
{
  match At(s.board, m.src)
  case Empty => s
  case Occ(p) =>
    // en passant: pawn moves diagonally onto an empty square, captured pawn is beside m.src
    var isEp := p.kind == Pawn && m.src.c != m.dst.c && At(s.board, m.dst) == Empty;
    // castling: king moves two files
    var isCastle := p.kind == King && Abs(m.dst.c - m.src.c) == 2;
    // a capture removes a piece: either one stands on the destination, or it is en passant
    var isCapture := At(s.board, m.dst) != Empty || isEp;
    // if promoting, swap the pawn for the promoted piece
    var placed := match m.promo
                  case Some(k) => Occ(Piece(p.color, k))
                  case None => Occ(p);
    var b1 := Put(Put(s.board, m.src, Empty), m.dst, placed);
    var b2 := if isEp then Put(b1, Sq(m.src.r, m.dst.c), Empty) else b1;
    // slide the rook across when castling
    var b3 :=
      if isCastle && m.dst.c == 6 then
        Put(Put(b2, Sq(m.src.r, 7), Empty), Sq(m.src.r, 5), Occ(Piece(p.color, Rook)))
      else if isCastle && m.dst.c == 2 then
        Put(Put(b2, Sq(m.src.r, 0), Empty), Sq(m.src.r, 3), Occ(Piece(p.color, Rook)))
      else b2;
    // set en passant target square on a double pawn push, otherwise clear it
    var newEp :=
      if p.kind == Pawn && Abs(m.dst.r - m.src.r) == 2
      then Some(Sq((m.src.r + m.dst.r) / 2, m.src.c))
      else None;
    var newRights := ClearRights(ClearRights(s.rights, m.src), m.dst);
    var newSide := Opp(s.side);
    var newHalf := if p.kind == Pawn || isCapture then 0 else s.halfmove + 1;
    var newFull := if s.side == Black then s.fullmove + 1 else s.fullmove;
    var newKey := Key(b3, newSide, newRights, newEp);
    State(b3, newSide, newRights, newEp, newHalf, newFull, s.history + [newKey])
}


// --- PART 6: LEGALITY SPECIFICATION ---

function KingsideRight(rt: Rights, c: Color): bool { if c == White then rt.wk else rt.bk }
function QueensideRight(rt: Rights, c: Color): bool { if c == White then rt.wq else rt.bq }

// destination square can't hold one of our own pieces
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

// reaching the last rank requires choosing N/B/R/Q; any other rank must have promo == None
predicate PromoOk(c: Color, m: Move)
{
  if m.dst.r == PromoRow(c) then
    (match m.promo
     case Some(k) => k == Knight || k == Bishop || k == Rook || k == Queen
     case None => false)
  else m.promo == None
}

// pawn movement: 1 step forward, 2 steps from start rank, diagonal capture, or en passant
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

// castling: king and rook on home squares, rights intact, path empty,
// and king isn't in check, crossing check, or landing in check
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

// checks if piece p can move from m.src to m.dst according to its movement rules
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

// pseudo-legal: valid piece geometry and target square, ignoring self-check
ghost predicate PseudoLegal(s: State, m: Move)
{
  OnBoard(m.src) && OnBoard(m.dst) && m.src != m.dst &&
  match At(s.board, m.src)
  case Empty => false
  case Occ(p) => p.color == s.side && LandingOk(s, m) && PieceRule(s, p, m)
}

// a move is legal iff it's pseudo-legal and doesn't leave our king in check
ghost predicate Legal(s: State, m: Move)
{
  PseudoLegal(s, m) && !InCheck(Apply(s, m).board, s.side)
}


// --- PART 7: LOOP IMPLEMENTATION (PROVED AGAINST THE SPEC) ---

// walks step-by-step from a toward b to verify no piece blocks the ray
method PathClearImpl(bd: seq<Cell>, a: Square, b: Square) returns (ok: bool)
  ensures ok <==> PathClear(bd, a, b)
{
  var n := Steps(a, b);
  var k := 1;
  while k < n
    invariant 1 <= k
    invariant n <= 1 || k <= n
    // everything checked before step k was empty
    invariant forall j {:trigger At(bd, Sq(a.r + j * Sign(b.r - a.r), a.c + j * Sign(b.c - a.c)))} ::
                1 <= j < k && j < n ==>
                At(bd, Sq(a.r + j * Sign(b.r - a.r), a.c + j * Sign(b.c - a.c))) == Empty
  {
    if At(bd, Sq(a.r + k * Sign(b.r - a.r), a.c + k * Sign(b.c - a.c))) != Empty {
      // give the prover the exact blocking square index so it knows PathClear is false
      assert 1 <= k < Steps(a, b);
      assert At(bd, Sq(a.r + k * Sign(b.r - a.r), a.c + k * Sign(b.c - a.c))) != Empty;
      return false;
    }
    k := k + 1;
  }
  return true;
}

// executable version of Attacks: checks if piece on f hits t
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

// scans all 64 squares to see if any attacker piece hits t
method IsAttackedImpl(bd: seq<Cell>, t: Square, attacker: Color) returns (ok: bool)
  ensures ok <==> IsAttacked(bd, t, attacker)
{
  var i := 0;
  while i < 64
    invariant 0 <= i <= 64
    invariant forall j :: 0 <= j < i ==> !Attacks(bd, SqOf(j), t, attacker)
  {
    var a := AttacksImpl(bd, SqOf(i), t, attacker);
    if a { return true; }
    i := i + 1;
  }
  return false;
}

// finds color c's king on the board and checks if the opponent attacks it
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

// executable castling check
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

// main move validator: checks pseudo-legality, applies move on a copy, and checks king safety
method IsLegalImpl(s: State, m: Move) returns (ok: bool)
  ensures ok <==> Legal(s, m)
{
  var pl := IsPseudoLegalImpl(s, m);
  if !pl { return false; }
  var after := Apply(s, m);
  var chk := InCheckImpl(after.board, s.side);
  return !chk;
}


// --- PART 8: MOVE GENERATOR AND THEOREMS ---

const PromoOpts: seq<Option<Kind>> :=
  [None, Some(Knight), Some(Bishop), Some(Rook), Some(Queen)]

// proves that every legal move has on-board coordinates and a valid promotion option
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

// index <-> square bijection helpers for the generator proofs
lemma IdxOfSqOf(i: int)
  requires 0 <= i < 64
  ensures OnBoard(SqOf(i)) && Idx(SqOf(i)) == i
{}

lemma SqOfIdx(s: Square)
  requires OnBoard(s)
  ensures 0 <= Idx(s) < 64 && SqOf(Idx(s)) == s
{}

// tries all 5 promotion options for a given (src, dst) pair
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
    invariant forall m :: (Legal(s, m) && m.src == SqOf(i) && m.dst == SqOf(j)
                           && m.promo in PromoOpts[..k]) ==> m in ms
  {
    var cand := Move(SqOf(i), SqOf(j), PromoOpts[k]);
    var ok := IsLegalImpl(s, cand);
    if ok { ms := ms + [cand]; }
    assert PromoOpts[..k + 1] == PromoOpts[..k] + [PromoOpts[k]];
    k := k + 1;
  }
  assert PromoOpts[..5] == PromoOpts;
  forall m | Legal(s, m) && m.src == SqOf(i) && m.dst == SqOf(j)
    ensures m in ms
  {
    LegalIsCandidate(s, m);
  }
}

// generates all legal moves starting from square i
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
    invariant forall jj :: 0 <= jj < j ==>
      forall m :: Legal(s, m) && m.src == SqOf(i) && m.dst == SqOf(jj) ==> m in ms
  {
    var part := GenFromTo(s, i, j);
    ms := ms + part;
    j := j + 1;
  }
  forall m | Legal(s, m) && m.src == SqOf(i)
    ensures m in ms
  {
    LegalIsCandidate(s, m);
    SqOfIdx(m.dst);
  }
}

// whenever there's a legal move on the board, add it to the moves list
// postconditions prove both soundness (no illegal moves) and completeness (no missed moves)
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

// checkmate: in check with 0 legal moves
method IsCheckmate(s: State) returns (b: bool)
  ensures b <==> (InCheck(s.board, s.side) && forall m :: !Legal(s, m))
{
  var moves := GenLegal(s);
  var chk := InCheckImpl(s.board, s.side);
  if |moves| == 0 {
    assert forall m :: !Legal(s, m);
  } else {
    assert moves[0] in moves;
    assert Legal(s, moves[0]);
  }
  return chk && |moves| == 0;
}

// stalemate: not in check with 0 legal moves
method IsStalemate(s: State) returns (b: bool)
  ensures b <==> (!InCheck(s.board, s.side) && forall m :: !Legal(s, m))
{
  var moves := GenLegal(s);
  var chk := InCheckImpl(s.board, s.side);
  if |moves| == 0 {
    assert forall m :: !Legal(s, m);
  } else {
    assert moves[0] in moves;
    assert Legal(s, moves[0]);
  }
  return !chk && |moves| == 0;
}

// safety lemmas
lemma LegalNeverLeavesKingInCheck(s: State, m: Move)
  requires Legal(s, m)
  ensures !InCheck(Apply(s, m).board, s.side)
{}

lemma ApplyKeepsBoardSize(s: State, m: Move)
  ensures |Apply(s, m).board| == |s.board|
{}

lemma LegalMovePassesTurn(s: State, m: Move)
  requires Legal(s, m)
  ensures Apply(s, m).side == Opp(s.side)
{
  assert PseudoLegal(s, m);
}


// --- PART 9: DRAW RULES, MOVE COUNTERS, GAME STATUS ---

// how many times the key k appears in the list h.
// defined recursively: look at the last element, then at everything before it
function Count(h: seq<Key>, k: Key): nat
  decreases |h|
{
  if |h| == 0 then 0
  else Count(h[..|h| - 1], k) + (if h[|h| - 1] == k then 1 else 0)
}

// fifty-move rule: 100 plies (50 moves by each side) with no pawn move and no capture
predicate FiftyMoveDraw(s: State)
{
  s.halfmove >= 100
}

// square color parity: even (0) or odd (1)
function SqColor(i: int): int { (i / 8 + i % 8) % 2 }

predicate IsMinor(k: Kind) { k == Knight || k == Bishop }

// spec: true iff no Pawns, Rooks, or Queens exist, and either:
//   - at most 1 minor piece is on the board (K vs K, K+N vs K, K+B vs K), OR
//   - there are no knights and all bishops share the same square color parity
ghost predicate InsufficientMaterial(s: State)
{
  // 1. No heavy pieces or pawns
  (forall i :: 0 <= i < 64 ==>
    match At(s.board, SqOf(i))
    case Empty => true
    case Occ(p) => p.kind == King || IsMinor(p.kind))
  &&
  (
    // Case A: at most one minor piece total on the board
    (forall i, j :: 0 <= i < j < 64 ==>
      !(match At(s.board, SqOf(i)) { case Occ(p1) => IsMinor(p1.kind) case Empty => false } &&
        match At(s.board, SqOf(j)) { case Occ(p2) => IsMinor(p2.kind) case Empty => false }))
    ||
    // Case B: zero knights, and all bishops stand on squares of identical color parity
    ((forall i :: 0 <= i < 64 ==> At(s.board, SqOf(i)) != Occ(Piece(White, Knight)) &&
                                  At(s.board, SqOf(i)) != Occ(Piece(Black, Knight))) &&
     (forall i, j :: 0 <= i < 64 && 0 <= j < 64 ==>
       (match At(s.board, SqOf(i)) { case Occ(p1) => p1.kind == Bishop case Empty => false } &&
        match At(s.board, SqOf(j)) { case Occ(p2) => p2.kind == Bishop case Empty => false })
       ==> SqColor(i) == SqColor(j)))
  )
}

// executable single-pass detector proved strictly equivalent to InsufficientMaterial(s)
method IsInsufficientMaterialImpl(s: State) returns (ok: bool)
  ensures ok <==> InsufficientMaterial(s)
{
  var knights := 0;
  var bishops := 0;
  var bColor := -1;
  var i := 0;

  while i < 64
    invariant 0 <= i <= 64
    invariant knights >= 0 && bishops >= 0
    invariant knights == 0 ==> forall j :: 0 <= j < i ==>
      At(s.board, SqOf(j)) != Occ(Piece(White, Knight)) &&
      At(s.board, SqOf(j)) != Occ(Piece(Black, Knight))
    invariant bishops == 0 ==> forall j :: 0 <= j < i ==>
      match At(s.board, SqOf(j)) { case Occ(p) => p.kind != Bishop case Empty => true }
    invariant bishops > 0 ==> (bColor == 0 || bColor == 1) &&
      forall j :: 0 <= j < i ==>
        (match At(s.board, SqOf(j)) { case Occ(p) => p.kind == Bishop case Empty => false })
        ==> SqColor(j) == bColor
    invariant forall j :: 0 <= j < i ==>
      match At(s.board, SqOf(j)) { case Empty => true case Occ(p) => p.kind == King || IsMinor(p.kind) }
    invariant knights + bishops <= 1 ==>
      forall j1, j2 :: 0 <= j1 < j2 < i ==>
        !(match At(s.board, SqOf(j1)) { case Occ(p1) => IsMinor(p1.kind) case Empty => false } &&
          match At(s.board, SqOf(j2)) { case Occ(p2) => IsMinor(p2.kind) case Empty => false })
    invariant knights + bishops > 1 ==>
      exists j1, j2 :: 0 <= j1 < j2 < i &&
        match At(s.board, SqOf(j1)) { case Occ(p1) => IsMinor(p1.kind) case Empty => false } &&
        match At(s.board, SqOf(j2)) { case Occ(p2) => IsMinor(p2.kind) case Empty => false }
  {
    match At(s.board, SqOf(i)) {
      case Empty =>
      case Occ(p) =>
        if p.kind == Pawn || p.kind == Rook || p.kind == Queen {
          return false;
        } else if p.kind == Knight {
          if knights > 0 || bishops > 0 { return false; }
          knights := knights + 1;
        } else if p.kind == Bishop {
          var c := SqColor(i);
          if knights > 0 { return false; }
          if bishops == 0 {
            bColor := c;
          } else if c != bColor {
            return false;
          }
          bishops := bishops + 1;
        }
    }
    i := i + 1;
  }
  return true;
}

// threefold repetition: the current position has occurred at least 3 times.
// the history already includes the current position, so we count it directly
predicate ThreefoldRepetition(s: State)
{
  Count(s.history, KeyOf(s)) >= 3
}

// a pawn move or a capture: exactly the moves that reset the fifty-move clock.
// (en passant is a pawn move, so it is covered by the pawn case)
predicate ResetsClock(s: State, m: Move)
{
  match At(s.board, m.src)
  case Empty => false
  case Occ(p) => p.kind == Pawn || At(s.board, m.dst) != Empty
}

// proves Apply keeps the counters and history exactly as the rules say
lemma ApplyUpdatesCounters(s: State, m: Move)
  requires Legal(s, m)
  ensures Apply(s, m).halfmove == (if ResetsClock(s, m) then 0 else s.halfmove + 1)
  ensures Apply(s, m).fullmove == (if s.side == Black then s.fullmove + 1 else s.fullmove)
  ensures |Apply(s, m).history| == |s.history| + 1
  ensures Apply(s, m).history[..|s.history|] == s.history
  ensures Apply(s, m).history[|s.history|] == KeyOf(Apply(s, m))
{
  assert PseudoLegal(s, m);
}

// executable counting, proved equal to the recursive definition
method CountImpl(h: seq<Key>, k: Key) returns (n: nat)
  ensures n == Count(h, k)
{
  n := 0;
  var i := 0;
  while i < |h|
    invariant 0 <= i <= |h|
    invariant n == Count(h[..i], k)
  {
    // dropping the last element of the prefix h[..i+1] gives the prefix h[..i]
    assert h[..i + 1][..i] == h[..i];
    assert h[..i + 1][i] == h[i];
    if h[i] == k { n := n + 1; }
    i := i + 1;
  }
  assert h[..|h|] == h;
}

datatype Status = Ongoing | Checkmate | Stalemate | DrawInsufficientMaterial | DrawFiftyMove | DrawRepetition

// spec: the status of a position. checkmate and stalemate come first (a mate
// on the 100th ply still counts as mate), then the draw rules
ghost function StatusSpec(s: State): Status
{
  if InCheck(s.board, s.side) && (forall m :: !Legal(s, m)) then Checkmate
  else if !InCheck(s.board, s.side) && (forall m :: !Legal(s, m)) then Stalemate
  else if FiftyMoveDraw(s) then DrawFiftyMove
  else if InsufficientMaterial(s) then DrawInsufficientMaterial
  else if ThreefoldRepetition(s) then DrawRepetition
  else Ongoing
}

// executable status check, proved equal to StatusSpec
method GameStatus(s: State) returns (st: Status)
  ensures st == StatusSpec(s)
{
  var mate := IsCheckmate(s);
  if mate { return Checkmate; }
  var stale := IsStalemate(s);
  if stale { return Stalemate; }
  var insuff := IsInsufficientMaterialImpl(s);
  if insuff { return DrawInsufficientMaterial; }
  if s.halfmove >= 100 { return DrawFiftyMove; }
  var n := CountImpl(s.history, KeyOf(s));
  if n >= 3 { return DrawRepetition; }
  return Ongoing;
}


// --- PART 10: RUNNABLE PERFT & GAME TESTS (UNVERIFIED) ---

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

// the starting position: halfmove 0, fullmove 1, history holds just this position
function StartState(): State
{
  var b := seq(64, i requires 0 <= i < 64 => StartCell(i));
  var r := Rights(true, true, true, true);
  State(b, White, r, None, 0, 1, [Key(b, White, r, None)])
}

// counts leaf nodes at 'depth' to cross-check move generation against known perft numbers
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

// reads a run of digits starting at index start; returns the number and the
// index of the first character after the digits
method ParseNat(fen: string, start: int) returns (n: int, next: int)
  requires 0 <= start
  ensures start <= next
{
  n := 0;
  var i := start;
  while i < |fen| && '0' <= fen[i] <= '9'
    invariant start <= i
  {
    n := n * 10 + ((fen[i] as int) - ('0' as int));
    i := i + 1;
  }
  return n, i;
}

// parses a FEN string into a State (mirrors fen_to_game in file_handling.c)
// fen fields: placement, side, castling, en passant, halfmove clock, fullmove number
method ParseFen(fen: string) returns (s: State)
{
  var board: seq<Cell> := seq(64, i => Empty);
  var r := 7;
  var c := 0;
  var i := 0;
  // piece placement from rank 8 (r = 7) down to rank 1
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
  // side to move
  i := i + 1;
  var side := if i < |fen| && fen[i] == 'b' then Black else White;
  i := i + 2;
  if i > |fen| { i := |fen|; }
  // castling rights
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
  // en passant square: a square like e3, or '-' for none
  i := i + 1;
  var ep: Option<Square> := None;
  if i + 1 < |fen| && 'a' <= fen[i] <= 'h' {
    ep := Some(Sq((fen[i + 1] as int) - ('1' as int), (fen[i] as int) - ('a' as int)));
    i := i + 2;
  } else {
    i := i + 1;
  }
  // halfmove clock, then fullmove number (defaults 0 and 1 if missing)
  i := i + 1;
  var half: int;
  half, i := ParseNat(fen, i);
  i := i + 1;
  var full: int;
  full, i := ParseNat(fen, i);
  if full == 0 { full := 1; }
  var raw := State(board, side, rights, ep, half, full, []);
  return raw.(history := [KeyOf(raw)]);
}

// plays a move written like "g1f3" (no promotion); prints a warning if it is illegal
method Play(s: State, mv: string) returns (t: State)
  requires |mv| == 4
{
  var m := Move(Sq((mv[1] as int) - ('1' as int), (mv[0] as int) - ('a' as int)),
                Sq((mv[3] as int) - ('1' as int), (mv[2] as int) - ('a' as int)), None);
  var ok := IsLegalImpl(s, m);
  if !ok { print "WARNING: illegal move ", mv, "\n"; }
  return Apply(s, m);
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
  // standard perft benchmark positions
  PerftFen("start   ", "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", 2, [20, 400]);
  PerftFen("kiwipete", "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", 2, [48, 2039]);
  PerftFen("position3", "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", 3, [14, 191, 2812]);
  PerftFen("position4", "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1", 2, [6, 264]);
  PerftFen("position5", "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8", 2, [44, 1486]);

  // checkmate and stalemate sanity checks
  var mated := ParseFen("rnb1kbnr/pppp1ppp/8/4p3/6Pq/5P2/PPPPP2P/RNBQKBNR w KQkq - 1 3");
  var m1 := IsCheckmate(mated);
  print "fool's mate, White to move, checkmate? ", m1, "  (expected true)\n";
  var stale := ParseFen("7k/5Q2/6K1/8/8/8/8/8 b - - 0 1");
  var m2 := IsStalemate(stale);
  print "queen+king vs king, Black to move, stalemate? ", m2, "  (expected true)\n";
  var m3 := IsCheckmate(StartState());
  print "start position, checkmate? ", m3, "  (expected false)\n";

  // move counters: halfmove clock and fullmove number
  var t0 := StartState();
  var t1 := Play(t0, "e2e4");
  print "after e2e4: halfmove ", t1.halfmove, ", fullmove ", t1.fullmove, "  (expected 0, 1)\n";
  var t2 := Play(t1, "e7e5");
  print "after e7e5: halfmove ", t2.halfmove, ", fullmove ", t2.fullmove, "  (expected 0, 2)\n";
  var t3 := Play(t2, "g1f3");
  print "after g1f3: halfmove ", t3.halfmove, ", fullmove ", t3.fullmove, "  (expected 1, 2)\n";
  var t4 := Play(t3, "b8c6");
  print "after b8c6: halfmove ", t4.halfmove, ", fullmove ", t4.fullmove, "  (expected 2, 3)\n";

  // fifty-move rule: a rook move that is not a pawn move or capture takes 99 to 100
  var f0 := ParseFen("4k3/8/8/8/8/8/8/R3K3 w Q - 99 50");
  var fs0 := GameStatus(f0);
  print "halfmove 99 status: ", fs0, "  (expected Ongoing)\n";
  var f1 := Play(f0, "a1a2");
  var fs1 := GameStatus(f1);
  print "after a1a2 halfmove ", f1.halfmove, " status: ", fs1, "  (expected 100, DrawFiftyMove)\n";

  // threefold repetition: both sides shuffle a knight out and back, twice
  var r0 := StartState();
  var r1 := Play(r0, "g1f3");
  var r2 := Play(r1, "g8f6");
  var r3 := Play(r2, "f3g1");
  var r4 := Play(r3, "f6g8");
  var rs4 := GameStatus(r4);
  print "start position seen twice: ", rs4, "  (expected Ongoing)\n";
  var r5 := Play(r4, "g1f3");
  var r6 := Play(r5, "g8f6");
  var r7 := Play(r6, "f3g1");
  var r8 := Play(r7, "f6g8");
  var rs8 := GameStatus(r8);
  print "start position seen three times: ", rs8, "  (expected DrawRepetition)\n";
}
