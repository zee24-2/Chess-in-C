# Chess in C

#### Video Demo: 

#### Description:

**Chess in C** is a full-featured command-line chess engine and game implemented entirely in the C programming language, supporting both **two-player local matches** and **single-player games against an AI opponent** across five difficulty levels. The goal of this project was to construct a robust, self-contained chess engine and interactive console interface from scratch, adhering strictly to the official rules of international chess (FIDE standards). The system incorporates complete move validation, state tracking, check and checkmate detection, stalemate recognition, the fifty-move and threefold repetition draw rules, pawn promotions, castling, en passant, and game persistence through standard Forsyth–Edwards Notation (FEN).

The project is designed with modularity and clean architectural boundaries in mind. Core functionality is segmented into dedicated modules for move generation, game mechanics, AI search and evaluation, FEN serialization, and safe file/input parsing. The user interface provides a clear 8x8 terminal board oriented to the active or human player, indicators for turns, check warnings, and AI moves, and a line-buffered input parser that accepts coordinate notation alongside game-management commands.

---

### File Overview and Implementation Details

The codebase comprises seven primary source and header files, along with a `Makefile`, organized into distinct logical components:

#### 1. `chess.c`

This file serves as the main entry point for the executable. Intentionally minimal, it contains only the `main` function. It allocates the top-level `Game` structure, calls `init_game(&g)` to configure the starting board and initial state, and delegates control to the interactive game loop by calling `play(&g)`. Keeping the main driver lean ensures complete decoupling between program lifecycle management and the internal game mechanics.

#### 2. `gameplay.h`

The primary header file defines all foundational data types, constants, and function prototypes governing chess logic:

* **Constants and Macros**: Defines player turn identifiers (`WHITE = 0`, `BLACK = 1`), maximum move capacity (`MAX_MOVES = 256`), maximum position history (`MAX_HISTORY = 1024`), and the boundary verification macro `IN(r, c)` ensuring array indices remain within `0` and `7`.
* **`Game` struct**: Encapsulates the entire chess match state:
* `board[8][8]`: A two-dimensional character array representing the 64 squares.
* `side`: An integer tracking whether it is White's or Black's turn.
* `castle`: A bitmask tracking castling permissions (1 for White Kingside, 2 for White Queenside, 4 for Black Kingside, 8 for Black Queenside).
* `ep_r`, `ep_c`: Coordinates of the active en passant target square (set to -1 if inactive).
* `halfmove`: Counter for the fifty-move clock, tracking plies since the last pawn advance or piece capture.
* `fullmove`: Number of full turns completed in the match (incremented after Black moves).
* `history[MAX_HISTORY][72]` and `history_count`: Stores compact position keys (board layout, active side, castling rights, and en passant square) to detect threefold repetition draws.


* **`Move` and `MoveList` structs**: Define individual move records containing source coordinates (`fr`, `fc`), destination coordinates (`tr`, `tc`), and an optional pawn promotion character (`promo`). `MoveList` maintains a fixed-size buffer of `Move` records and an active count.
* **Prototypes**: Declares routines for board setup, terminal rendering, move generation, attack detection, king safety verification, repetition tracking, move execution, and the primary gameplay loop.

#### 3. `gameplay.c`

The heart of the chess engine, implementing board operations, rule enforcement, and the interactive user interface:

* **Board Display and Safe Input Parsing**: `init_game` sets up the standard layout using uppercase characters for White pieces (`P`, `N`, `B`, `R`, `Q`, `K`) and lowercase for Black (`p`, `n`, `b`, `r`, `q`, `k`), with empty squares marked as dots (`.`). `print_board` renders the current board state oriented from either White's or Black's perspective. `ask_choice` and `play` use bounded line-based reading (`fgets` and `strtol`) to prevent buffer overflows and leftover newline bugs, while `parse_move` validates and converts coordinate strings like `e2e4` or `e7e8q` into zero-indexed numeric coordinates.
* **Move Generation**:
* `gen_jumper`: Generates pseudo-legal moves for fixed-offset leaping pieces (knights and kings) using directional delta tables (`KN_DR`, `KN_DC`, `KG_DR`, `KG_DC`).
* `gen_slider`: Traces straight rays for sliding pieces (rooks along orthogonals, bishops along diagonals, and queens along both) until reaching the board edge or encountering an obstacle.
* `gen_pawn`: Manages pawn mechanics, including single-square advances, two-square initial leaps, diagonal captures, promotion handling across all four promotion options (queen, rook, bishop, knight), and en passant captures based on target square tracking.
* `gen_castle`: Checks castling eligibility for kingside and queenside, verifying that the king and rook have not moved, intervening squares are empty, and neither the king's initial square, transit squares, nor destination squares are under enemy attack.


* **Threat Detection and King Safety**:
* `is_attacked`: Determines if a given target square is attacked by a designated opposing color by casting reverse rays and jump checks from the target square.
* `in_check`: Locates the specified player's king on the board and tests whether its position is under attack.


* **Legality, Draw Rules, and Status Verification**:
* `gen_legal`: Generates all pseudo-legal candidate moves, applies each speculatively to a copied game state, and discards any move that leaves the moving player's king in check before appending legal castling moves.
* `game_status` and `is_threefold`: Evaluates terminal game states after every turn (including immediately after loading a FEN file), detecting checkmate, stalemate, the fifty-move rule (`halfmove >= 100`), and threefold repetition (`is_threefold`).
* `apply_move`: Executes verified moves by updating board squares, handling pawn promotions, adjusting castling rights when rooks or kings move or get captured, updating en passant targets, maintaining move counters, alternating active sides, and recording the resulting position in `history`.


* **Game Setup and Interactive Loop (`play`)**: Lets the user choose between **Play a friend** (auto-flipping the board each turn) or **Play the computer** (choosing from 5 difficulty levels corresponding to search depths 2 through 6, and playing as White, Black, or Random).

#### 4. `ai.h` & `ai.c`

Implements the computer opponent using a minimax search engine:

* **Static Board Evaluation (`static_eval`)**: Evaluates material balance using standard centipawn weights (Pawn = 100, Knight = 300, Bishop = 300, Rook = 500, Queen = 900) alongside positional bonuses (+50 centipawns) for central control by pawns, knights, and bishops.
* **Move Ordering (`move_value`, `order`)**: Uses insertion sort with Most Valuable Victim – Least Valuable Attacker (MVV-LVA) heuristics, en passant bonuses, and promotion bonuses to prioritize promising captures first and maximize alpha-beta pruning efficiency.
* **Negamax Search with Alpha-Beta Pruning (`negamax`, `best_move`)**: Recursively explores the game tree up to the selected difficulty depth (`depth` 2–6), recognizing checkmate distances (`-MATE + ply`), stalemate, fifty-move draws, and threefold repetition draws during search.

#### 5. `file_handling.h` & `file_handling.c`

Implements FEN serialization, strict validation, and disk persistence:

* `game_to_fen`: Encodes the board rank-by-rank from row 8 down to row 1, collapsing consecutive empty squares into digit counts, appending side to move (`w`/`b`), castling availability flags (`KQkq` or `-`), en passant coordinates (`a3` through `h6` or `-`), and halfmove/fullmove numbers.
* `fen_to_game`: Safely parses and validates incoming FEN strings before modifying the active `Game` state. It rejects malformed rank lengths, invalid piece characters, pawns placed on the 1st or 8th ranks, missing or duplicate kings, invalid castling/en passant fields, negative move clocks, trailing garbage, and illegal positions where the non-moving side is already in check.
* `save_game` and `open_game`: Provide safe disk persistence using bounded `fgets` reading and formatted FEN writing so matches can be saved and resumed cleanly—even if the loaded FEN is already in check, checkmate, or stalemate.

---

### Design Decisions and Technical Trade-offs

During development, several architectural choices and trade-offs were evaluated:

1. **Board Representation (2D Char Array vs. Bitboards)**:
A 64-bit integer bitboard architecture is standard in high-performance competitive chess engines. However, for a readable, self-contained terminal chess game in C, clarity, ease of debugging, and maintainability were prioritized. An 8x8 two-dimensional character array (`char board[8][8]`) maps directly to ranks and files, making terminal rendering straightforward and move transformations intuitive without requiring bitwise manipulation for board layout.
2. **AI Search Algorithm (Negamax with Alpha-Beta Pruning & MVV-LVA)**:
Instead of a plain minimax search, the AI uses a fail-soft Negamax formulation with alpha-beta pruning and MVV-LVA move ordering. Searching captures and promotions first significantly narrows the branching factor, allowing the engine to reach depth 5–6 in pure C within a couple of seconds without needing transposition tables.
3. **Save State Serialization & Strict Validation (FEN)**:
Rather of inventing a custom binary format, standard Forsyth–Edwards Notation (FEN) was adopted so saved games can be inspected or imported into external chess analysis tools (such as Lichess or Chess.com). `fen_to_game` parses into a temporary `Game` struct and verifies king counts, pawn ranks, and check legality before committing the state, ensuring corrupt or impossible FEN files cannot crash the engine or leave the game in an unplayable state.
4. **Move Validation Strategy (Pseudo-Legal Simulation vs. Ray-Tracing Pins)**:
To enforce king safety (ensuring a player cannot move into check or fail to parry an existing check), the engine generates pseudo-legal moves and tests each on a copied game state (`Game copy = *g`). While analytical pin calculation avoids copying, duplicating the `Game` struct in C is fast and eliminates edge-case bugs such as discovered checks via en passant captures. Since `Game` holds the repetition history array, search rollouts naturally evaluate repetition draws on their local copies without polluting the main match history.
5. **Input Syntax (Coordinate Notation vs. Standard Algebraic Notation)**:
Standard Algebraic Notation (SAN), such as `Nf3` or `exd5`, requires complex disambiguation logic. Long coordinate notation (`e2e4`, `g1f3`, `e7e8q`) keeps user input unambiguous and parsing resilient. For castling, entering the king's two-square move (`e1g1` or `e1c1`) triggers castling automatically. If a pawn reaches the final rank, the user can append their promotion choice (`e7e8q`, `e7e8r`, `e7e8b`, `e7e8n`), defaulting to a queen if omitted.

---

### Compilation and Execution

To compile the project using `make` (recommended):

```bash
make

```

Or manually with `gcc`:

```bash
gcc -Wall -Wextra -std=c99 -O2 chess.c gameplay.c file_handling.c ai.c -o chess

```

To start the game:

```bash
./chess

```

#### Gameplay Commands:

* **Setup**: Choose between **Play a friend** or **Play the computer** (with 5 difficulty levels and White/Black/Random side selection).
* **Make a move**: Enter source and destination squares, e.g., `e2e4`, `g1f3`, or `e7e8q` for promotion.
* **Castle**: Move the king two squares toward the rook, e.g., `e1g1` (White kingside) or `e1c1` (White queenside).
* **Save game**: Type `save <filename>` (e.g., `save match1.fen`).
* **Load game**: Type `load <filename>` (e.g., `load match1.fen`).
* **Quit**: Type `quit`.