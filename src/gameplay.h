#ifndef GAMEPLAY_H
#define GAMEPLAY_H

#define WHITE 0
#define BLACK 1
#define MAX_MOVES 256
#define MAX_HISTORY 1024
#define IN(r,c) ((r) >= 0 && (r) < 8 && (c) >= 0 && (c) < 8)

typedef struct {
    char board[8][8];
    int side;       // WHITE (0) or BLACK (1)
    int castle;     // 1 = wk, 2 = wq, 4 = bk, 8 = bq
    int ep_r, ep_c; // en passant target square, -1,-1 if none
    int halfmove;
    int fullmove;
    char history[MAX_HISTORY][72]; // Position keys for threefold repetition
    int history_count;
} Game;

typedef struct {
    int fr, fc;
    int tr, tc;
    char promo; // 0, or 'q' 'r' 'b' 'n' to promote (all lower)
} Move;

typedef struct {
    Move move[MAX_MOVES];
    int count;
} MoveList;

void init_game(Game *g);
void print_board(const Game *g, int bottom);
int colour_of(char p);
int parse_move(const char *s, Move *m);
void add_move(MoveList *l, int fr, int fc, int tr, int tc);
void add_pawn_move(MoveList *l, int fr, int fc, int tr, int tc);
void gen_jumper(const Game *g, MoveList *l, int r, int c, const int *dr, const int *dc, int n);
void gen_slider(const Game *g, MoveList *l, int r, int c, const int *dr, const int *dc, int n);
void gen_pawn(const Game *g, MoveList *l, int r, int c);
void gen_castle(const Game *g, MoveList *l);
void gen_all(const Game *g, MoveList *l);
void update_rights(Game *g, int r, int c);
void record_position(Game *g);
int is_threefold(const Game *g);
int is_insufficient_material(const Game *g);
void apply_move(Game *g, Move m);
char piece_for(char upper, int by);
int is_attacked(const Game *g, int r, int c, int by);
int in_check(const Game *g, int colour);
void gen_legal(const Game *g, MoveList *out);
int game_status(const Game *g);
int is_legal(const Game *g, Move m);
void play(Game *g);
void clear_screen(void);

#endif