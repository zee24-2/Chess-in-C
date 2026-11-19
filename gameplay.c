//gameplay.c

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include "gameplay.h"
#include "file_handling.h"
#include <ai.h>

void clear_screen(void) {
    system("clear");
}

void init_game (Game *g){
    const char *start[8] = {
        "RNBQKBNR",
        "PPPPPPPP",
        "........",
        "........",
        "........",
        "........",
        "pppppppp",
        "rnbqkbnr"
    };
    for (int r = 7; r >=0; r--){
        for (int c = 0; c < 8; c++){
            g->board[r][c] = start [r][c];
        }
    }
    g->side = WHITE;
    g->castle = 15;
    g->ep_r = g->ep_c = -1;
    g->halfmove = 0;
    g->fullmove = 1;
}
//initialize the gameboard, only ran once


void print_board (const Game *g){
    printf ("\n");
    for (int r = 7; r >= 0; r--){
        printf ("%d  ", r+1);
        for (int c = 0; c<8; c++){
            printf ("%c ", g->board[r][c]);
        }
        printf ("\n");
    }
    printf ("\n   a b c d e f g h\n\n");
}
//print the current board, it is run in every move iteration

int colour_of (char p) {
    return isupper((unsigned char)p) ? WHITE : BLACK;
}
//if the character is in uppercase, it is White
//if the character is in lowercase, it is Black

int parse_move (const char *s, Move *m){
    int n = strlen (s);
    if (n < 4 || n > 5) return 0;
    if (s[0] < 'a' || s[0] > 'h' || s[2] < 'a' || s[2] > 'h') return 0;
    if (s[1] < '1' || s[1] > '8' || s[3] < '1' || s[3] > '8') return 0;
    m->fc = s[0] - 'a';
    m->tc = s[2] - 'a';
    m->fr = (s[1] - '0') - 1;
    m->tr = (s[3] - '0') - 1;
    m->promo = 0;
    if (n==5){
        char p = tolower((unsigned char)s[4]);
        if (p != 'q' && p != 'r' && p != 'b' && p != 'n') return 0;
        m->promo = p;
    }
    return 1;
}
//checks and converts moves like a4e4 into numeric values

const int KN_DR[8] = {-2,-2,-1,-1, 1, 1, 2, 2};
const int KN_DC[8] = {-1, 1,-2, 2,-2, 2,-1, 1};
const int KG_DR[8] = {-1,-1,-1, 0, 0, 1, 1, 1};
const int KG_DC[8] = {-1, 0, 1,-1, 1,-1, 0, 1};
const int DG_DR[4] = {-1,-1, 1, 1};
const int DG_DC[4] = {-1, 1,-1, 1};
const int OR_DR[4] = {-1, 1, 0, 0};
const int OR_DC[4] = { 0, 0,-1, 1};


//whenever theres a valid move, add it to the moves array
//increment count to store how many moves are there


void add_move(MoveList *l, int fr, int fc, int tr, int tc) {
    Move m = {fr, fc, tr, tc, 0};
    l->move[l->count++] = m;
}

void add_pawn_move(MoveList *l, int fr, int fc, int tr, int tc) {
    if (tr == 0 || tr == 7) {
        const char promos[4] = {'q', 'r', 'b', 'n'};
        for (int i = 0; i < 4; i++) {
            Move m = {fr, fc, tr, tc, promos[i]};
            l->move[l->count++] = m;
        }
    } 
    else {
        Move m = {fr, fc, tr, tc, 0};
        l->move[l->count++] = m;
    }
}

void gen_jumper (const Game *g, MoveList *l, int r, int c, const int *dr, const int *dc, int n){
    for (int i = 0; i < n; i++){
        int nr = r + dr[i], nc = c + dc[i];
        if (!IN (nr, nc)) continue;
        char t = g->board[nr][nc];
        if (t == '.' || colour_of(t) != g->side)
            add_move (l, r, c, nr, nc);
    }
}

void gen_slider (const Game *g, MoveList *l, int r, int c, const int *dr, const int *dc, int n){
    for (int i = 0; i < n; i++){
        int nr = r + dr[i], nc = c + dc[i];
        while (IN(nr, nc)){
            char t = g->board[nr][nc];
            if (t == '.'){
                add_move (l, r, c, nr, nc);
            }
            else{
                if (colour_of(t) != g->side) add_move (l, r, c, nr, nc);
                break;
            }
            nr = nr + dr[i];
            nc = nc + dc[i];
        }
    }
}

void gen_pawn (const Game *g, MoveList *l, int r, int c){
    int dir = (g->side == WHITE) ? 1 : -1;
    int start = (g->side == WHITE) ? 1 : 6;
    int nr = r + dir;
    if (!IN(nr, c)) return;

    if (g->board[nr][c] == '.'){
        add_pawn_move (l, r, c, nr, c);
        if (r ==start && g->board[r + 2*dir][c] == '.'){
            add_move (l, r, c, r + 2*dir, c);
        }
    }

    for (int dc = -1; dc <= 1; dc += 2) {
        int nc = c + dc;
        if (!IN(nr, nc)) continue;
        char t = g->board[nr][nc];
        if (t != '.' && colour_of(t) != g->side)
            add_pawn_move(l, r, c, nr, nc);
        else if (t == '.' && nr == g->ep_r && nc == g->ep_c)
            add_move(l, r, c, nr, nc);   // en passant
    }
}

void gen_castle (const Game *g, MoveList *l){
    int r = (g->side == WHITE) ? 0 : 7;
    int opp = 1-g->side;
    char king = (g->side == WHITE) ? 'K' : 'k';
    char rook = (g->side == WHITE) ? 'R' : 'r';
    int ks = (g->side == WHITE) ? 1 : 4;
    int qs = (g->side == WHITE) ? 2 : 8;

    if (g->board[r][4] != king) return;
    if (is_attacked (g, r, 4, opp)) return;

    if ((g->castle & ks) && g->board[r][7] == rook && 
    g->board [r][5] == '.' && g->board [r][6] == '.' &&
    !is_attacked (g, r, 5, opp) && !is_attacked (g, r, 6, opp))
    add_move (l, r, 4, r, 6);

    if ((g->castle & qs) && g->board[r][0] == rook && 
    g->board [r][1] == '.' && g->board [r][2] == '.' && g->board [r][3] == '.' &&
    !is_attacked (g, r, 3, opp) && !is_attacked (g, r, 2, opp))
    add_move (l, r, 4, r, 2);
}

void gen_all (const Game *g, MoveList *l){
    l->count = 0;
    for (int r = 0; r < 8; r++){
        for (int c = 0; c < 8; c++){
            char p = g->board[r][c];
            if (p == '.' || colour_of(p) != g->side) continue;
            switch(p){
                case 'P':
                case 'p': gen_pawn (g, l , r, c); break;
                case 'N':
                case 'n': gen_jumper (g, l, r, c, KN_DR, KN_DC, 8); break;
                case 'K':
                case 'k': gen_jumper(g, l, r, c, KG_DR, KG_DC, 8); break;
                case 'B':
                case 'b': gen_slider(g, l, r, c, DG_DR, DG_DC, 4); break;
                case 'R':
                case 'r': gen_slider(g, l, r, c, OR_DR, OR_DC, 4); break;
                case 'Q':
                case 'q': gen_slider(g, l, r, c, DG_DR, DG_DC, 4);
                          gen_slider(g, l, r, c, OR_DR, OR_DC, 4); break;
            }
        }
    }
}

void update_rights(Game *g, int r, int c) {
    if (r == 0 && c == 4) g->castle &= ~3;
    if (r == 7 && c == 4) g->castle &= ~12;
    if (r == 0 && c == 0) g->castle &= ~2;
    if (r == 0 && c == 7) g->castle &= ~1;
    if (r == 7 && c == 0) g->castle &= ~8;
    if (r == 7 && c == 7) g->castle &= ~4;
}

void apply_move (Game *g, Move m){
    char p = g->board[m.fr][m.fc];
    int is_pawn = (p == 'P' || p == 'p');
    int capture = (g->board[m.tr][m.tc] != '.');

    if (is_pawn && m.fc != m.tc && !capture){
        g->board [m.fr][m.tc] = '.';
        capture = 1;
    }

    if ((p == 'K' || p == 'k') && abs (m.tc - m.fc) == 2){
        if (m.tc == 6) {g->board[m.fr][5] = g->board[m.fr][7]; g->board[m.fr][7] = '.'; }
        else if (m.tc == 2) { g->board[m.fr][3] = g->board[m.fr][0]; g->board[m.fr][0] = '.'; }
    }


    g->board[m.tr][m.tc] = p;
    g->board[m.fr][m.fc] = '.';
    
    if (m.promo){
        g->board[m.tr][m.tc] = (g->side == WHITE) ? toupper(m.promo) : m.promo;
    }

    update_rights (g, m.fr, m.fc);
    update_rights (g, m.tr, m.tc);

    g->ep_r = g->ep_c = -1;
    if (is_pawn && abs(m.tr - m.fr) == 2){
        g->ep_r = (m.fr + m.tr)/2;
        g->ep_c = m.fc;
    }

    if (is_pawn || capture) g->halfmove = 0; else g->halfmove++;
    if (g->side == BLACK) g->fullmove++;

    g->side = 1 - g->side;
}

//if i want like the piece for king by white, it should return K otherwise k
char piece_for(char upper, int by) {
    if (by == WHITE) {
        return upper;
    } else {
        return tolower(upper);
    }
}

//point of is_attacked is to see if the king is in check
int is_attacked (const Game *g, int r, int c, int by){
    int pr = (by == WHITE) ? r-1 : r+1;
    //pawn row
    //a white pawn will attack upward
    //if victim is at r, then white pawn is r-1

    //Pawns:
    for (int dc = -1; dc <= 1; dc+=2){
        if (IN(pr, c+dc) && 
        g-> board [pr][c+dc] == piece_for('P', by)) return 1;
    }

    //Knights:
    for (int i = 0; i<8; i++){
        int nr = r + KN_DR[i];
        int nc = c + KN_DC[i];
        if (IN(nr, nc) &&
        g-> board [nr][nc] == piece_for('N', by)) return 1;
    }

    //King:
    for (int i = 0; i<8; i++){
        int nr = r + KG_DR[i];
        int nc = c + KG_DC[i];
        if (IN(nr, nc) &&
        g-> board [nr][nc] == piece_for('K', by)) return 1;
    }

    //Diagonals:
    for (int i = 0; i<4; i++){
        int nr = r + DG_DR[i];
        int nc = c + DG_DC[i];
        while (IN(nr, nc)){
            char t = g->board[nr][nc];
            if (t != '.'){
                if (t == piece_for ('B', by) || t == piece_for ('Q', by)) return 1;
                break;
            }
            nr += DG_DR[i];
            nc += DG_DC[i];
        }
    }

    //Orthogonals:
    for (int i = 0; i<4; i++){
        int nr = r + OR_DR[i];
        int nc = c + OR_DC[i];
        while (IN(nr, nc)){
            char t = g->board[nr][nc];
            if (t != '.'){
                if (t == piece_for ('R', by) || t == piece_for ('Q', by)) return 1;
                break;
            }
            nr += OR_DR[i];
            nc += OR_DC[i];
        }
    }
    return 0;
}

int in_check (const Game *g, int colour){
    char king = (colour == WHITE) ? 'K' : 'k';
    for (int r = 0; r<8; r++){
        for (int c = 0; c<8; c++){
            if (g->board[r][c] == king){
                return is_attacked (g, r, c, 1-colour);
            }
        }
    }
    return 0; //only when no king found
}

void gen_legal (const Game *g, MoveList *out){
    MoveList all;
    gen_all (g, &all);
    out->count = 0;
    for (int i = 0; i<all.count; i++) {
        Game copy = *g;
        apply_move (&copy, all.move[i]);
        if (!in_check(&copy, g->side)){
            out -> move [out->count++] = all.move[i];
        }
    }
    gen_castle (g, out);
}

// returns 0 = game continues, 1 = checkmate, 2 = stalemate
int game_status(const Game *g) {
    MoveList l;
    gen_legal(g, &l);
    if (l.count > 0) return 0;
    return in_check(g, g->side) ? 1 : 2;
}

int is_legal(const Game *g, Move m) {
    MoveList l;
    gen_legal(g, &l);
    for (int i = 0; i < l.count; i++)
        if (l.move[i].fr == m.fr && l.move[i].fc == m.fc &&
            l.move[i].tr == m.tr && l.move[i].tc == m.tc &&
            l.move[i].promo == m.promo)
            return 1;
    return 0;
}


void play(Game *g) {
    char input[50];
    char filename[50];
    while (1){
        clear_screen();
        print_board(g);
        int st = game_status(g);
        if (st == 1) { printf("Checkmate! %s wins.\n", g->side == WHITE ? "Black" : "White"); break; }
        if (st == 2) { printf("Stalemate. Draw.\n"); break; }
        if (g->halfmove >= 100) { printf("Draw by 50-move rule.\n"); break; }
        if (in_check(g, g->side)) printf("Check!\n");

        while (1){
            printf("%s to move (e.g. e2e4, 'save f', 'load f', 'quit'): ", 
                g->side == WHITE ? "White" : "Black");
            if (scanf("%49s", input) != 1) return;
            if (strcmp(input, "quit") == 0) return;


            if (strcmp(input, "save") == 0) {
                scanf("%49s", filename);
                printf(save_game(filename, g) ? "Saved.\n" : "Could not save.\n");
                continue;
            }
            if (strcmp(input, "load") == 0) {
                scanf("%49s", filename);
                if (open_game(filename, g)) break;
                else printf("Could not load.\n");
                continue;
            }


            Move m;
            if (parse_move(input, &m)) {
                if (!is_legal(g, m)) m.promo = 'q'; 
                if (is_legal(g, m)) { apply_move(g, m); break; }
                else printf("Illegal Move. Try Again.\n");
            }
            else printf("Illegal Move. Try Again.\n");
        }
    }
}