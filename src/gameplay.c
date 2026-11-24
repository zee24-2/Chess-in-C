#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>
#include "gameplay.h"
#include "file_handling.h"
#include "ai.h"

void clear_screen(void) {
    system("clear");
}

// Generates a compact key (board + side + castling + ep) for repetition detection
static void make_pos_key(const Game *g, char out[72]) {
    int k = 0;
    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            out[k++] = g->board[r][c];
        }
    }
    out[k++] = (g->side == WHITE) ? 'w' : 'b';
    out[k++] = (char)('0' + g->castle);
    out[k++] = (char)('a' + g->ep_c);
    out[k++] = (char)('1' + g->ep_r);
    out[k] = '\0';
}

void record_position(Game *g) {
    if (g->history_count < MAX_HISTORY) {
        make_pos_key(g, g->history[g->history_count++]);
    }
}

int is_threefold(const Game *g) {
    if (g->history_count < 5) return 0; // Impossible before 5 plies
    const char *current = g->history[g->history_count - 1];
    int matches = 1;
    // Step backwards by 2 (same side to move), stopping at last irreversible move
    int limit = g->history_count - 1 - g->halfmove;
    if (limit < 0) limit = 0;

    for (int i = g->history_count - 3; i >= limit; i -= 2) {
        if (strcmp(current, g->history[i]) == 0) {
            matches++;
            if (matches >= 3) return 1;
        }
    }
    return 0;
}

void init_game(Game *g) {
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
    for (int r = 7; r >= 0; r--) {
        for (int c = 0; c < 8; c++) {
            g->board[r][c] = start[r][c];
        }
    }
    g->side = WHITE;
    g->castle = 15;
    g->ep_r = g->ep_c = -1;
    g->halfmove = 0;
    g->fullmove = 1;
    g->history_count = 0;
    record_position(g);
}

void print_board(const Game *g, int bottom) {
    printf("\n");
    for (int i = 0; i < 8; i++) {
        int r = (bottom == WHITE) ? 7 - i : i;
        printf("%d  ", r + 1);
        for (int j = 0; j < 8; j++) {
            int c = (bottom == WHITE) ? j : 7 - j;
            printf("%c ", g->board[r][c]);
        }
        printf("\n");
    }
    if (bottom == WHITE) printf("\n   a b c d e f g h\n\n");
    else                 printf("\n   h g f e d c b a\n\n");
}

int colour_of(char p) {
    return isupper((unsigned char)p) ? WHITE : BLACK;
}

int parse_move(const char *s, Move *m) {
    if (!s || !m) return 0;
    size_t n = strlen(s);
    if (n < 4 || n > 5) return 0;
    if (s[0] < 'a' || s[0] > 'h' || s[2] < 'a' || s[2] > 'h') return 0;
    if (s[1] < '1' || s[1] > '8' || s[3] < '1' || s[3] > '8') return 0;
    m->fc = s[0] - 'a';
    m->tc = s[2] - 'a';
    m->fr = (s[1] - '0') - 1;
    m->tr = (s[3] - '0') - 1;
    m->promo = 0;
    if (n == 5) {
        char p = (char)tolower((unsigned char)s[4]);
        if (p != 'q' && p != 'r' && p != 'b' && p != 'n') return 0;
        m->promo = p;
    }
    return 1;
}

const int KN_DR[8] = {-2,-2,-1,-1, 1, 1, 2, 2};
const int KN_DC[8] = {-1, 1,-2, 2,-2, 2,-1, 1};
const int KG_DR[8] = {-1,-1,-1, 0, 0, 1, 1, 1};
const int KG_DC[8] = {-1, 0, 1,-1, 1,-1, 0, 1};
const int DG_DR[4] = {-1,-1, 1, 1};
const int DG_DC[4] = {-1, 1,-1, 1};
const int OR_DR[4] = {-1, 1, 0, 0};
const int OR_DC[4] = { 0, 0,-1, 1};

void add_move(MoveList *l, int fr, int fc, int tr, int tc) {
    if (l->count >= MAX_MOVES) return;
    Move m = {fr, fc, tr, tc, 0};
    l->move[l->count++] = m;
}

void add_pawn_move(MoveList *l, int fr, int fc, int tr, int tc) {
    if (tr == 0 || tr == 7) {
        const char promos[4] = {'q', 'r', 'b', 'n'};
        for (int i = 0; i < 4; i++) {
            if (l->count >= MAX_MOVES) return;
            Move m = {fr, fc, tr, tc, promos[i]};
            l->move[l->count++] = m;
        }
    } else {
        add_move(l, fr, fc, tr, tc);
    }
}

void gen_jumper(const Game *g, MoveList *l, int r, int c, const int *dr, const int *dc, int n) {
    for (int i = 0; i < n; i++) {
        int nr = r + dr[i], nc = c + dc[i];
        if (!IN(nr, nc)) continue;
        char t = g->board[nr][nc];
        if (t == '.' || colour_of(t) != g->side)
            add_move(l, r, c, nr, nc);
    }
}

void gen_slider(const Game *g, MoveList *l, int r, int c, const int *dr, const int *dc, int n) {
    for (int i = 0; i < n; i++) {
        int nr = r + dr[i], nc = c + dc[i];
        while (IN(nr, nc)) {
            char t = g->board[nr][nc];
            if (t == '.') {
                add_move(l, r, c, nr, nc);
            } else {
                if (colour_of(t) != g->side) add_move(l, r, c, nr, nc);
                break;
            }
            nr += dr[i];
            nc += dc[i];
        }
    }
}

void gen_pawn(const Game *g, MoveList *l, int r, int c) {
    int dir = (g->side == WHITE) ? 1 : -1;
    int start = (g->side == WHITE) ? 1 : 6;
    int nr = r + dir;
    if (!IN(nr, c)) return;

    if (g->board[nr][c] == '.') {
        add_pawn_move(l, r, c, nr, c);
        if (r == start && g->board[r + 2 * dir][c] == '.') {
            add_move(l, r, c, r + 2 * dir, c);
        }
    }

    for (int dc = -1; dc <= 1; dc += 2) {
        int nc = c + dc;
        if (!IN(nr, nc)) continue;
        char t = g->board[nr][nc];
        if (t != '.' && colour_of(t) != g->side)
            add_pawn_move(l, r, c, nr, nc);
        else if (t == '.' && nr == g->ep_r && nc == g->ep_c)
            add_move(l, r, c, nr, nc);
    }
}

void gen_castle(const Game *g, MoveList *l) {
    int r = (g->side == WHITE) ? 0 : 7;
    int opp = 1 - g->side;
    char king = (g->side == WHITE) ? 'K' : 'k';
    char rook = (g->side == WHITE) ? 'R' : 'r';
    int ks = (g->side == WHITE) ? 1 : 4;
    int qs = (g->side == WHITE) ? 2 : 8;

    if (g->board[r][4] != king) return;
    if (is_attacked(g, r, 4, opp)) return;

    if ((g->castle & ks) && g->board[r][7] == rook &&
        g->board[r][5] == '.' && g->board[r][6] == '.' &&
        !is_attacked(g, r, 5, opp) && !is_attacked(g, r, 6, opp))
        add_move(l, r, 4, r, 6);

    if ((g->castle & qs) && g->board[r][0] == rook &&
        g->board[r][1] == '.' && g->board[r][2] == '.' && g->board[r][3] == '.' &&
        !is_attacked(g, r, 3, opp) && !is_attacked(g, r, 2, opp))
        add_move(l, r, 4, r, 2);
}

void gen_all(const Game *g, MoveList *l) {
    l->count = 0;
    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            char p = g->board[r][c];
            if (p == '.' || colour_of(p) != g->side) continue;
            switch (p) {
                case 'P':
                case 'p': gen_pawn(g, l, r, c); break;
                case 'N':
                case 'n': gen_jumper(g, l, r, c, KN_DR, KN_DC, 8); break;
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

void apply_move(Game *g, Move m) {
    char p = g->board[m.fr][m.fc];
    int is_pawn = (p == 'P' || p == 'p');
    int capture = (g->board[m.tr][m.tc] != '.');

    if (is_pawn && m.fc != m.tc && !capture) {
        g->board[m.fr][m.tc] = '.';
        capture = 1;
    }

    if ((p == 'K' || p == 'k') && abs(m.tc - m.fc) == 2) {
        if (m.tc == 6) { g->board[m.fr][5] = g->board[m.fr][7]; g->board[m.fr][7] = '.'; }
        else if (m.tc == 2) { g->board[m.fr][3] = g->board[m.fr][0]; g->board[m.fr][0] = '.'; }
    }

    g->board[m.tr][m.tc] = p;
    g->board[m.fr][m.fc] = '.';

    if (m.promo) {
        g->board[m.tr][m.tc] = (g->side == WHITE) ? (char)toupper((unsigned char)m.promo) : m.promo;
    }

    update_rights(g, m.fr, m.fc);
    update_rights(g, m.tr, m.tc);

    g->ep_r = g->ep_c = -1;
    if (is_pawn && abs(m.tr - m.fr) == 2) {
        g->ep_r = (m.fr + m.tr) / 2;
        g->ep_c = m.fc;
    }

    if (is_pawn || capture) g->halfmove = 0;
    else g->halfmove++;

    if (g->side == BLACK) g->fullmove++;

    g->side = 1 - g->side;
    record_position(g);
}

char piece_for(char upper, int by) {
    return (by == WHITE) ? upper : (char)tolower((unsigned char)upper);
}

int is_attacked(const Game *g, int r, int c, int by) {
    int pr = (by == WHITE) ? r - 1 : r + 1;

    for (int dc = -1; dc <= 1; dc += 2) {
        if (IN(pr, c + dc) && g->board[pr][c + dc] == piece_for('P', by)) return 1;
    }

    for (int i = 0; i < 8; i++) {
        int nr = r + KN_DR[i], nc = c + KN_DC[i];
        if (IN(nr, nc) && g->board[nr][nc] == piece_for('N', by)) return 1;
    }

    for (int i = 0; i < 8; i++) {
        int nr = r + KG_DR[i], nc = c + KG_DC[i];
        if (IN(nr, nc) && g->board[nr][nc] == piece_for('K', by)) return 1;
    }

    for (int i = 0; i < 4; i++) {
        int nr = r + DG_DR[i], nc = c + DG_DC[i];
        while (IN(nr, nc)) {
            char t = g->board[nr][nc];
            if (t != '.') {
                if (t == piece_for('B', by) || t == piece_for('Q', by)) return 1;
                break;
            }
            nr += DG_DR[i];
            nc += DG_DC[i];
        }
    }

    for (int i = 0; i < 4; i++) {
        int nr = r + OR_DR[i], nc = c + OR_DC[i];
        while (IN(nr, nc)) {
            char t = g->board[nr][nc];
            if (t != '.') {
                if (t == piece_for('R', by) || t == piece_for('Q', by)) return 1;
                break;
            }
            nr += OR_DR[i];
            nc += OR_DC[i];
        }
    }
    return 0;
}

int in_check(const Game *g, int colour) {
    char king = (colour == WHITE) ? 'K' : 'k';
    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            if (g->board[r][c] == king) {
                return is_attacked(g, r, c, 1 - colour);
            }
        }
    }
    return 0;
}

void gen_legal(const Game *g, MoveList *out) {
    MoveList all;
    gen_all(g, &all);
    out->count = 0;
    for (int i = 0; i < all.count; i++) {
        Game copy = *g;
        apply_move(&copy, all.move[i]);
        if (!in_check(&copy, g->side)) {
            out->move[out->count++] = all.move[i];
        }
    }
    gen_castle(g, out);
}

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

// Safe line-based integer choice parser
static int ask_choice(const char *prompt, int max) {
    char line[64];
    while (1) {
        printf("%s", prompt);
        if (!fgets(line, sizeof(line), stdin)) return -1;
        char *endptr;
        long val = strtol(line, &endptr, 10);
        while (isspace((unsigned char)*endptr)) endptr++;
        if (endptr != line && *endptr == '\0' && val >= 1 && val <= max) {
            return (int)val;
        }
        printf("Please enter a number from 1 to %d.\n", max);
    }
}

void play(Game *g) {
    char line[128];
    char filename[64];
    char ai_msg[64] = "";

    int mode = ask_choice("1) Play a friend\n2) Play the computer\nChoose: ", 2);
    if (mode == -1) return;

    int comp = -1;
    int depth = 0;
    int bottom = WHITE;

    if (mode == 2) {
        int level = ask_choice("\nDifficulty:\n1) Beginner\n2) Easy\n3) Medium\n4) Hard\n5) Max\nChoose: ", 5);
        if (level == -1) return;
        int depths[5] = {2, 3, 4, 5, 6};
        depth = depths[level - 1];

        int colour = ask_choice("\nPlay as:\n1) White\n2) Black\n3) Random\nChoose: ", 3);
        if (colour == -1) return;
        if (colour == 3) {
            srand((unsigned int)time(NULL));
            colour = rand() % 2 + 1;
            snprintf(ai_msg, sizeof(ai_msg), "You are %s.", colour == 1 ? "White" : "Black");
        }
        int human = (colour == 1) ? WHITE : BLACK;
        comp = 1 - human;
        bottom = human;
    }

    while (1) {
        clear_screen();
        if (mode == 1) bottom = g->side;
        print_board(g, bottom);
        if (ai_msg[0] != '\0') {
            printf("%s\n", ai_msg);
            ai_msg[0] = '\0';
        }

        int st = game_status(g);
        if (st == 1) { printf("Checkmate! %s wins.\n", g->side == WHITE ? "Black" : "White"); break; }
        if (st == 2) { printf("Stalemate. Draw.\n"); break; }
        if (g->halfmove >= 100) { printf("Draw by 50-move rule.\n"); break; }
        if (is_threefold(g)) { printf("Draw by threefold repetition.\n"); break; }
        if (in_check(g, g->side)) printf("Check!\n");

        if (g->side == comp) {
            printf("AI is thinking...\n");
            fflush(stdout);
            Move m = best_move(g, depth);
            snprintf(ai_msg, sizeof(ai_msg), "AI played: %c%d%c%d%c",
                     'a' + m.fc, m.fr + 1,
                     'a' + m.tc, m.tr + 1,
                     m.promo ? m.promo : '\0');
            apply_move(g, m);
            continue;
        }

        while (1) {
            printf("%s to move (e.g. e2e4, 'save <file>', 'load <file>', 'quit'): ",
                   g->side == WHITE ? "White" : "Black");
            if (!fgets(line, sizeof(line), stdin)) return;

            // Strip trailing newline and whitespace
            line[strcspn(line, "\r\n")] = '\0';
            char *cmd = line;
            while (isspace((unsigned char)*cmd)) cmd++;
            size_t len = strlen(cmd);
            while (len > 0 && isspace((unsigned char)cmd[len - 1])) cmd[--len] = '\0';

            if (len == 0) continue;
            if (strcmp(cmd, "quit") == 0) return;

            if (strncmp(cmd, "save", 4) == 0 && (cmd[4] == '\0' || isspace((unsigned char)cmd[4]))) {
                if (sscanf(cmd + 4, "%63s", filename) == 1) {
                    printf(save_game(filename, g) ? "Saved.\n" : "Could not save.\n");
                } else {
                    printf("Usage: save <filename>\n");
                }
                continue;
            }

            if (strncmp(cmd, "load", 4) == 0 && (cmd[4] == '\0' || isspace((unsigned char)cmd[4]))) {
                if (sscanf(cmd + 4, "%63s", filename) == 1) {
                    if (open_game(filename, g)) {
                        snprintf(ai_msg, sizeof(ai_msg), "Loaded %s.", filename);
                        break; // Re-evaluates board, check, checkmate, and draw rules immediately
                    } else {
                        printf("Could not load (invalid file or illegal FEN position).\n");
                    }
                } else {
                    printf("Usage: load <filename>\n");
                }
                continue;
            }

            Move m;
            if (parse_move(cmd, &m)) {
                if (!is_legal(g, m) && m.promo == 0) m.promo = 'q';
                if (is_legal(g, m)) {
                    apply_move(g, m);
                    break;
                } else {
                    printf("Illegal Move. Try Again.\n");
                }
            } else {
                printf("Invalid input format. Try Again.\n");
            }
        }
    }
}