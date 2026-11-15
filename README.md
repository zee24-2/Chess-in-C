# Chess in C
#### Video Demo: <keep this space empty>
#### Description:

**Chess in C** is a full-featured, two-player command-line chess game implemented entirely in the C programming language. The goal of this project was to construct a robust, self-contained chess engine and interactive console interface from scratch, adhering strictly to the official rules of international chess (FIDE standards). The system incorporates complete move validation, state tracking, check and checkmate detection, stalemate recognition, the fifty-move draw rule, pawn promotions, castling, en passant, and game persistence through standard Forsyth–Edwards Notation (FEN).

The project is designed with modularity and clean architectural boundaries in mind. Core functionality is segmented into dedicated modules for move generation, game mechanics, FEN serialization, and file I/O. The user interface provides a clear 8x8 terminal board rendered after every turn, an indicator of player turn and check warnings, and an input parser that accepts intuitive coordinate notation alongside game-management commands.

---

### File Overview and Implementation Details

The codebase comprises five primary source and header files, organized into distinct logical components:

#### 1. `chess.c`
This file serves as the main entry point for the executable. Intentionally minimal, it contains only the `main` function. It allocates the top-level `Game` structure, calls `init_game(&g)` to configure the starting board and initial state, and delegates control to the interactive game loop by calling `play(&g)`. Keeping the main driver lean ensures complete decoupling between program lifecycle management and the internal game mechanics.

#### 2. `gameplay.h`
The primary header file defines all foundational data types, constants, and function prototypes governing chess logic:
- **Constants and Macros**: Defines player turn identifiers (`WHITE = 0`, `BLACK = 1`), maximum move capacity (`MAX_MOVES = 256`), and the boundary verification macro `IN(r, c)` ensuring array indices remain within `0` and `7`.
- **`Game` struct**: Encapsulates the entire chess match state:
  - `board[8][8]`: A two-dimensional character array representing the 64 squares.
  - `side`: An integer tracking whether it is White's or Black's turn.
  - `castle`: A bitmask tracking castling permissions (1 for White Kingside, 2 for White Queenside, 4 for Black Kingside, 8 for Black Queenside).
  - `ep_r`, `ep_c`: Coordinates of the active en passant target square (set to -1 if inactive).
  - `halfmove`: Counter for the fifty-move clock, tracking plies since the last pawn advance or piece capture.
  - `fullmove`: Number of full turns completed in the match (incremented after Black moves).
- **`Move` and `MoveList` structs**: Define individual move records containing source coordinates (`fr`, `fc`), destination coordinates (`tr`, `tc`), and an optional pawn promotion character (`promo`). `MoveList` maintains a fixed-size buffer of `Move` records and an active count.
- **Prototypes**: Declares routines for board setup, terminal rendering, move generation, attack detection, king safety verification, move execution, and the primary gameplay loop.

#### 3. `gameplay.c`
The heart of the chess engine, spanning more than 400 lines of logic that implements board operations and rule enforcement:
- **Board Display and Parsing**: `init_game` sets up the classic standard layout using uppercase characters for White pieces (`P`, `N`, `B`, `R`, `Q`, `K`) and lowercase for Black (`p`, `n`, `b`, `r`, `q`, `k`), with empty squares marked as dots (`.`). `print_board` renders the current board state with row numbers (1 to 8) and column letters (a to h). `parse_move` converts coordinate strings like `e2e4` or promotion inputs like `e7e8q` into zero-indexed numeric coordinates.
- **Move Generation**:
  - `gen_jumper`: Generates pseudo-legal moves for fixed-offset leaping pieces (knights and kings) using directional delta tables (`KN_DR`, `KN_DC`, `KG_DR`, `KG_DC`).
  - `gen_slider`: Traces straight rays for sliding pieces (rooks along orthogonals, bishops along diagonals, and queens along both) until reaching the board edge or encountering an obstacle.
  - `gen_pawn`: Manages pawn mechanics, including single-square advances, two-square initial leaps, diagonal captures, promotion handling across all four promotion options (queen, rook, bishop, knight), and en passant captures based on target square tracking.
  - `gen_castle`: Checks castling eligibility for kingside and queenside, verifying that the king and rook have not moved, intervening squares are empty, and neither the king's initial square, transit squares, nor destination squares are under enemy attack.
- **Threat Detection and King Safety**:
  - `is_attacked`: Determines if a given target square is attacked by a designated opposing color. It casts reverse rays and jump checks from the target square to identify hostile pawns, knights, kings, diagonal sliders, or orthogonal sliders.
  - `in_check`: Locates the current player's king on the board and tests whether its position is under attack.
- **Legality and Status Verification**:
  - `gen_legal`: Implements full move validation by generating all pseudo-legal candidate moves, applying each speculatively to a copied game state, and discarding any move that leaves the moving player's king in check. Valid castling options are subsequently appended.
  - `game_status`: Tests whether legal moves exist for the active player. If no legal moves remain, it distinguishes between checkmate (king currently in check) and stalemate (king safe). It also verifies the 50-move rule condition (`halfmove >= 100`).
  - `apply_move`: Executes verified moves by updating board squares, handling pawn promotions, adjusting castling rights when rooks or kings move or get captured, resetting or updating en passant targets, maintaining move counters, and alternating active sides.
- **Interactive Game Loop (`play`)**: Drives the match inside a continuous loop, clearing the screen on every turn, rendering the board, reporting checks or terminal states, prompting the player, and parsing user commands.

#### 4. `file_handling.h`
Declares the serialization and disk persistence interface. Defines function signatures for converting a `Game` state to a standard FEN string (`game_to_fen`), restoring a `Game` state from a FEN string (`fen_to_game`), saving games to disk (`save_game`), and loading saved files (`open_game`).

#### 5. `file_handling.c`
Implements serialization and file I/O routines:
- `game_to_fen`: Encodes the board rank-by-rank from row 8 down to row 1, collapsing consecutive empty squares into digit counts, appending side to move (`w`/`b`), castling availability flags (`KQkq` or `-`), en passant coordinates (`a3` through `h6` or `-`), and halfmove/fullmove numbers.
- `fen_to_game`: Parses an incoming FEN string, populating the board matrix, decoding empty square counts, setting turn markers, reconstituting the castling bitmask, and parsing active en passant coordinates and clocks.
- `save_game` and `open_game`: Provide straightforward disk persistence by writing and reading formatted FEN records using standard C file operations (`fopen`, `fprintf`, `fscanf`, `fclose`), allowing players to store in-progress matches to any file and resume them seamlessly.

---

### Design Decisions and Technical Trade-offs

During development, several architectural choices and trade-offs were evaluated:

1. **Board Representation (2D Char Array vs. Bitboards)**:
   A 64-bit integer bitboard architecture is standard in high-performance competitive chess engines. However, for a human-versus-human terminal chess game in C, readability, simplicity of debugging, and maintainability were prioritized. An 8x8 two-dimensional character array (`char board[8][8]`) maps directly to ranks and files, making terminal rendering straightforward and move transformations intuitive without requiring bitwise manipulation for board layout.

2. **Save State Serialization (FEN vs. Custom Binary/Plaintext)**:
   Instead of inventing an ad-hoc custom file format or dumping raw structs, standard Forsyth–Edwards Notation (FEN) was adopted. FEN is the universal standard in chess software. By implementing FEN serialization, games saved from this application can be inspected, edited, or exported into standard chess tools and analysis boards (such as Lichess or Chess.com), providing interoperability and making test states easy to construct.

3. **Move Validation Strategy (Pseudo-Legal Simulation vs. Ray-Tracing Pins)**:
   To enforce king safety (ensuring a player cannot move into check or fail to parry an existing check), two approaches were considered: computing pinned pieces analytically or generating pseudo-legal moves and testing them on a copy of the board. The engine utilizes speculative execution via a copied game state (`Game copy = *g`). While analytical pin calculation can be slightly faster in engine trees, board copying in C is lightweight (a `Game` struct is only around 96 bytes) and dramatically reduces bugs in subtle edge cases, such as en passant discoveries or complex multi-piece checks.

4. **Input Syntax (Coordinate Notation vs. Standard Algebraic Notation)**:
   Standard Algebraic Notation (SAN), such as `Nf3`, `exd5`, or `O-O`, requires disambiguation logic based on which pieces can legally reach a square. To keep user input unambiguous and parsing clean and resilient, long coordinate notation (`e2e4`, `g1f3`, `e7e8q`) was selected. This eliminates ambiguity for both human players and the input parsing routine. For castling, entering the king's two-square move (`e1g1` or `e1c1`) triggers castling automatically. If a pawn reaches the final rank, the user can append their promotion choice (`e7e8q`, `e7e8r`, `e7e8b`, `e7e8n`), defaulting to a queen if omitted.

5. **Castling Rights as a Bitmask**:
   Rather than storing separate boolean flags for each rook and king, castling availability is maintained in a single integer bitmask (`1 = K`, `2 = Q`, `4 = k`, `8 = q`). This allows castling rights updates upon piece movements or captures to be expressed cleanly through bitwise operations (`&` and `~`), minimizing branching logic.

---

### Compilation and Execution

To compile the project using `gcc`, run the following command in the project directory:

```bash
gcc -Wall -Wextra -std=c99 chess.c gameplay.c file_handling.c -o chess
```

To start the game:

```bash
./chess
```

#### Gameplay Commands:
- **Make a move**: Enter source and destination squares, e.g., `e2e4`, `g1f3`, or `e7e8q` for promotion.
- **Castle**: Move the king two squares toward the rook, e.g., `e1g1` (White kingside) or `e1c1` (White queenside).
- **Save game**: Type `save <filename>` (e.g., `save match1.fen`).
- **Load game**: Type `load <filename>` (e.g., `load match1.fen`).
- **Quit**: Type `quit`.
