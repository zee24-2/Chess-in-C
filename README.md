```markdown
# Chess in C

![CI](https://github.com/zee24-2/Chess-in-C/actions/workflows/ci.yml/badge.svg)

A command-line chess engine and game written from scratch in C99, featuring local two-player mode, an alpha-beta Negamax AI opponent with phase-aware Piece-Square Tables across five difficulty levels, FEN persistence, and an independent formal specification and verified move/draw-rule implementation in Dafny.

```text
8  r n b q k b n r
7  p p p p p p p p
6  . . . . . . . .
5  . . . . . . . .
4  . . . . P . . .
3  . . . . . . . .
2  P P P P . P P P
1  R N B Q K B N R

   a b c d e f g h

AI played: e7e5
White to move (e.g. e2e4, 'save <file>', 'load <file>', 'quit'):

```

### Quick Start

```bash
# Build and launch the C engine
make
./chess

# Run the C perft and insufficient-material test suite
make test

# Verify all 44 proofs in Dafny (requires Dafny 4.11+)
dafny verify dafny/chess.dfy

```

---

### Description

**Chess in C** is a modular, zero-dependency C99 chess engine and interactive terminal game adhering to standard international chess rules. It supports local two-player matches (auto-flipping the board each turn) and single-player games against a Negamax AI opponent, incorporating full move validation, check/checkmate/stalemate detection, insufficient material draws, the fifty-move and threefold repetition draw rules, pawn promotion, castling, en passant, and Forsyth–Edwards Notation (FEN) save/load support.

Alongside the C codebase, `dafny/chess.dfy` provides a standalone formal specification and verified implementation of the core move rules, draw rules, move counters, and game-status logic in Dafny 4.11 (44 proofs, 0 errors). Both the C engine (`make test`) and the Dafny generator (`dafny run dafny/chess.dfy`) produce identical `perft` node counts across standard Chess Programming Wiki benchmark positions (`start`: 20 / 400 / 8,902; `kiwipete`: 48 / 2,039 / 97,862).

---

### What Is and Isn't Verified

The Dafny file (`dafny/chess.dfy`) serves as a formal methods companion to the C engine. To be precise about what is proved:

* **Proof of specification compliance, not chess itself:** Dafny proves that the loop-based implementations (`IsLegalImpl`, `GenLegal`, `IsInsufficientMaterialImpl`, `CountImpl`, `GameStatus`) strictly agree with the declarative logic specifications (`Legal`, `InsufficientMaterial`, `Count`, `StatusSpec`) across all possible board states and moves. That proves the implementation matches *this* specification—not that the specification itself is free of rule mistakes (which is why both engines are tested against published `perft` counts and endgame/draw scenarios).
* **Separate implementation, not C verification:** `dafny/chess.dfy` is an independent implementation written in Dafny, not a formal proof of the C source files in `src/`. Having two independently written implementations produce identical `perft` counts provides strong cross-validation.
* **Complete FIDE rule coverage in Dafny:** `dafny/chess.dfy` models core piece movement, pins/check, castling, en passant, promotion, checkmate, stalemate, insufficient material (`K vs K`, `K+N vs K`, `K+B vs K`, and same-colored `K+B vs K+B`), the fifty-move rule, threefold repetition, and halfmove/fullmove counters—matching the full ruleset of the C engine.
* **Draw claiming & en passant repetition keys:** Both the C and Dafny implementations treat fifty-move and threefold repetition draws as automatic once reached (rather than requiring a player claim), and include the en passant target square unconditionally in repetition keys (which can occasionally detect a repetition one move later than strict FIDE rules when no en passant capture is actually legal).
* **Unverified test harnesses:** `ParseFen`, `Perft`, and `Main` inside `dafny/chess.dfy` are executable test helpers and are not formally proved.

---

### File Overview and Implementation Details

The repository is organized into `src/`, `dafny/`, and `tests/`, accompanied by a `Makefile` and GitHub Actions CI workflow:

#### 1. `src/chess.c`

The main entry point for the executable. Intentionally minimal, it contains only the `main` function, allocating the top-level `Game` struct, calling `init_game(&g)` to configure the starting position, and delegating control to `play(&g)`.

#### 2. `src/gameplay.h`

Defines foundational data types, constants, and function prototypes governing chess logic:

* **Constants and Macros**: Defines turn identifiers (`WHITE = 0`, `BLACK = 1`), move list capacity (`MAX_MOVES = 256`), position history capacity (`MAX_HISTORY = 1024`), and the bounds macro `IN(r, c)`.
* **`Game` struct**: Encapsulates the match state:
* `board[8][8]`: Two-dimensional character array representing the 64 squares.
* `side`: Active player (`WHITE` or `BLACK`).
* `castle`: Bitmask tracking castling rights (`1` = White Kingside, `2` = White Queenside, `4` = Black Kingside, `8` = Black Queenside).
* `ep_r`, `ep_c`: Coordinates of the active en passant target square (`-1` if inactive).
* `halfmove`: Halfmove clock tracking plies since the last pawn push or capture.
* `fullmove`: Fullmove counter incremented after Black's turn.
* `history[MAX_HISTORY][72]` and `history_count`: Compact position keys (board, active side, castling rights, and en passant square) used to detect threefold repetition draws.


* **`Move` and `MoveList` structs**: Store source coordinates (`fr`, `fc`), destination coordinates (`tr`, `tc`), and an optional promotion character (`promo`).

#### 3. `src/gameplay.c`

Implements board operations, rule enforcement, and the interactive terminal interface:

* **Board Display and Safe Input Parsing**: `init_game` initializes the standard layout (`P`, `N`, `B`, `R`, `Q`, `K` for White; lowercase for Black; `.` for empty squares). `print_board` renders the 8x8 board oriented to the active or human player. `ask_choice` and `play` use bounded line-buffered reading (`fgets` and `strtol`) to prevent buffer overflows and leftover newline bugs, while `parse_move` validates coordinate strings (`e2e4`, `e7e8q`).
* **Move Generation**:
* `gen_jumper`: Generates pseudo-legal moves for knights and kings using offset tables (`KN_DR`, `KN_DC`, `KG_DR`, `KG_DC`).
* `gen_slider`: Traces rays along orthogonals and diagonals for rooks, bishops, and queens until hitting the board edge or an occupied square.
* `gen_pawn`: Handles single advances, double pushes from the starting rank, diagonal captures, all four promotion choices (`q`, `r`, `b`, `n`), and en passant captures.
* `gen_castle`: Verifies castling rights, unmoved king/rook placement, empty intervening squares, and that the king is not in check, crossing check, or landing in check.


* **King Safety, Draw Rules, and Status Verification**:
* `is_attacked` and `in_check`: Detect square attacks via reverse ray/jump checks and test whether the active king is under attack.
* `gen_legal`: Filters pseudo-legal moves by applying each candidate to a copied state (`Game copy = *g`) and discarding moves that leave the moving side's king in check before appending legal castling moves.
* `game_status`, `is_insufficient_material`, and `is_threefold`: Evaluate terminal states after every move (and immediately on FEN load), checking checkmate/stalemate before insufficient material (`K vs K`, `K+N vs K`, `K+B vs K`, and same-colored `K+B vs K+B`), fifty-move (`halfmove >= 100`), and threefold repetition draws.
* `apply_move`: Updates board squares, handles promotions, revokes spent castling rights, sets/clears en passant targets, updates move clocks, switches turns, and appends the position key to `history`.


* **Interactive Loop (`play`)**: Supports **Play a friend** (auto-flipping the board each turn) and **Play the computer** (depths 2–6, playing as White, Black, or Random).

#### 4. `src/ai.h` & `src/ai.c`

Implements the computer opponent using a minimax search engine:

* **Static Board Evaluation (`static_eval`, `pst_bonus`)**: Scores material balance (`Pawn = 100`, `Knight = 300`, `Bishop = 300`, `Rook = 500`, `Queen = 900`) combined with piece-specific Piece-Square Tables (PSTs) for pawns, knights, bishops, rooks, queens, and phase-switched king tables (middlegame king safety vs. endgame king centralization when non-pawn material drops to `<= 2600`).
* **Move Ordering (`move_value`, `order`)**: Uses insertion sort with Most Valuable Victim – Least Valuable Attacker (MVV-LVA) scoring, en passant bonuses, and promotion bonuses to search strong captures first and maximize alpha-beta cutoffs.
* **Negamax Search with Alpha-Beta Pruning (`negamax`, `best_move`)**: Recursively searches the game tree up to the chosen depth (`2`–`6`), scoring checkmate distances (`-MATE + ply`) and detecting stalemate, insufficient material, fifty-move, and repetition draws inside the search tree.

#### 5. `src/file_handling.h` & `src/file_handling.c`

Implements FEN serialization, validation, and disk persistence:

* `game_to_fen`: Encodes board ranks, active side, castling flags, en passant square, and halfmove/fullmove counters into standard FEN format.
* `fen_to_game`: Parses into a temporary `Game` struct and validates rank lengths, piece characters, pawns on the 1st/8th ranks, king counts, castling/en passant syntax, non-negative move counters, trailing tokens, and check legality before committing to the active game.
* `save_game` and `open_game`: Read and write FEN files safely with bounded `fgets` I/O.

#### 6. `dafny/chess.dfy` (Formal Verification in Dafny)

A formal specification and verified implementation of the core chess rules, draw rules, and move counters written in **Dafny 4.11** (44 proofs, 0 errors):

* **Declarative Logic Specification**: Defines chess geometry (`PathClear`), attack rules (`PieceAttacks`, `IsAttacked`, `InCheck`), state transitions (`Apply`), special moves (`CastleOK`, `PawnRule`, `PromoOk`), move legality (`PseudoLegal`, `Legal`), and draw conditions (`InsufficientMaterial`, `FiftyMoveDraw`, `ThreefoldRepetition`, `StatusSpec`).
* **Verified Loop Implementations**: Proves executable loop-based routines (`PathClearImpl`, `AttacksImpl`, `IsAttackedImpl`, `InCheckImpl`, `IsLegalImpl`, `IsInsufficientMaterialImpl`, `CountImpl`, `GameStatus`) equivalent to their specifications via loop invariants and Z3 theorem proving.
* **Soundness, Completeness & Counter Theorems**: Proves `GenLegal` returns *only* legal moves (soundness) and misses *no* legal moves (completeness), alongside `ApplyUpdatesCounters` (verifying halfmove, fullmove, and history updates on every legal move), `LegalNeverLeavesKingInCheck`, `ApplyKeepsBoardSize`, and `LegalMovePassesTurn`.
* **Perft & Draw Cross-Validation (`Main`)**: Includes an unverified FEN parser and `Perft` runner verifying standard benchmark counts alongside checkmate, stalemate, insufficient material, fifty-move draw, and threefold repetition test cases.

#### 7. `tests/perft.c` & `Makefile`

Automates compilation (`make`) and runs `perft` benchmarks and insufficient-material unit tests (`make test`) to confirm that the C move generator matches `dafny/chess.dfy` and published Chess Programming Wiki node counts.

---

### Design Decisions and Technical Trade-offs

1. **Board Representation (2D Char Array vs. Bitboards)**:
While 64-bit bitboards are standard in high-speed competitive engines, an 8x8 two-dimensional character array (`char board[8][8]`) maps directly to ranks and files, keeping terminal rendering straightforward and move logic readable and easy to debug.
2. **AI Search Algorithm (Negamax with Alpha-Beta Pruning, PSTs & MVV-LVA)**:
Fail-soft/fail-hard Negamax with alpha-beta pruning, MVV-LVA move ordering, and phase-switched Piece-Square Tables searches tactical captures first while guiding positional development and endgame king activity. Lower difficulty levels respond instantaneously, while depths 5–6 typically complete within a few seconds depending on position complexity.
3. **Save State Serialization & Validation (FEN)**:
Adopting standard Forsyth–Edwards Notation (FEN) allows saved positions to be inspected or loaded in external tools like Lichess or Chess.com. Parsing into a temporary `Game` struct ensures malformed or illegal FEN files are rejected cleanly without corrupting an active game.
4. **Move Validation Strategy (Copy-and-Test vs. Analytical Pin Tables)**:
Testing each pseudo-legal candidate on a copied `Game` struct (`Game copy = *g`) avoids complex pin/discovered-check edge cases (such as horizontal en passant pins) while automatically giving search rollouts an isolated repetition history.
5. **Formal Verification vs. Runtime Speed (`dafny/chess.dfy`)**:
In `dafny/chess.dfy`, `GenLegal` enumerates all $64 \times 64 \times 5$ candidate `(src, dst, promo)` triples and filters them with `IsLegalImpl`. While slower during `Perft` than piece-centric generation, uniform enumeration makes proving **completeness** (`forall m :: Legal(s, m) ==> m in moves`) clean and tractable for Z3.
6. **Input Syntax (Coordinate Notation vs. SAN)**:
Long coordinate notation (`e2e4`, `g1f3`, `e7e8q`) eliminates SAN disambiguation complexity and keeps command-line input unambiguous, defaulting pawn promotions to Queen (`q`) if the promotion piece is omitted.

---

### Compilation and Execution

#### C Chess Engine

Build using `make`:

```bash
make

```

Or compile manually with `gcc`:

```bash
gcc -Wall -Wextra -std=c99 -O2 src/chess.c src/gameplay.c src/file_handling.c src/ai.c -o chess

```

Start the game:

```bash
./chess

```

Run the C `perft` and insufficient-material test suite:

```bash
make test

```

#### Gameplay Commands

* **Setup**: Choose between **Play a friend** or **Play the computer** (5 difficulty levels, White/Black/Random side selection).
* **Make a move**: Enter source and destination squares, e.g., `e2e4`, `g1f3`, or `e7e8q` for promotion.
* **Castle**: Move the king two squares toward the rook, e.g., `e1g1` (White kingside) or `e1c1` (White queenside).
* **Save game**: Type `save <filename>` (e.g., `save match1.fen`).
* **Load game**: Type `load <filename>` (e.g., `load match1.fen`).
* **Quit**: Type `quit`.

#### Dafny Formal Verification (`dafny/chess.dfy`)

Requires **Dafny 4.x** (`dafny 4.11.0` tested).

Verify all 44 specifications, invariants, and theorems:

```bash
dafny verify dafny/chess.dfy

```

Compile and run the `Perft`, endgame, and draw-rule test suite:

```bash
dafny run dafny/chess.dfy

```
