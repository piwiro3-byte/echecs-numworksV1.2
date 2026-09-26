#include <eadk.h>
#include <stdlib.h>

using namespace EADK;

const int SQ = 24;
const int OX = 64;
const int OY = 24;

// Couleurs (Format Display::Color)
const Display::Color C_LIGHT(0xEDD8); 
const Display::Color C_DARK(0xAB55);  
const Display::Color C_CUR(0xFFE0);   
const Display::Color C_SEL(0x4DC0);   
const Display::Color C_MOVE(0x65BD);  
const Display::Color C_BG(0x10A2);    
const Display::Color C_WHITE(0xFFFF);
const Display::Color C_BLACK(0x0000);
const Display::Color C_RED(0xF800);

int board[8][8];

const int P_BONUS[8][8] = {
  {0,0,0,0,0,0,0,0},
  {1,1,1,1,1,1,1,1},
  {1,2,3,3,3,3,2,1},
  {1,3,5,6,6,5,3,1},
  {1,3,5,6,6,5,3,1},
  {1,2,3,3,3,3,2,1},
  {1,1,1,1,1,1,1,1},
  {0,0,0,0,0,0,0,0}
};

const int VALS[7] = {0, 10, 30, 30, 50, 90, 900};
const char* SYMBOLS[7] = {" ", "P", "N", "B", "R", "Q", "K"};

struct Pos { int r, c; };

void init_board() {
  int init[8][8] = {
    {-4,-2,-3,-5,-6,-3,-2,-4},
    {-1,-1,-1,-1,-1,-1,-1,-1},
    { 0, 0, 0, 0, 0, 0, 0, 0},
    { 0, 0, 0, 0, 0, 0, 0, 0},
    { 0, 0, 0, 0, 0, 0, 0, 0},
    { 0, 0, 0, 0, 0, 0, 0, 0},
    { 1, 1, 1, 1, 1, 1, 1, 1},
    { 4, 2, 3, 5, 6, 3, 2, 4}
  };
  for(int r = 0; r < 8; r++)
    for(int c = 0; c < 8; c++)
      board[r][c] = init[r][c];
}

int abs_val(int v) { return v < 0 ? -v : v; }

int get_moves(int r, int c, Pos moves[]) {
  int count = 0;
  int p = board[r][c];
  if (p == 0) return 0;
  bool is_w = (p > 0);
  int type = abs_val(p);

  if (type == 1) { // Pion
    int d = is_w ? -1 : 1;
    if (r+d >= 0 && r+d < 8 && board[r+d][c] == 0) {
      moves[count++] = {r+d, c};
      int start_r = is_w ? 6 : 1;
      if (r == start_r && board[r+2*d][c] == 0) {
        moves[count++] = {r+2*d, c};
      }
    }
    for (int dc = -1; dc <= 1; dc += 2) {
      int nr = r + d, nc = c + dc;
      if (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
        int t = board[nr][nc];
        if (t != 0 && ((is_w && t < 0) || (!is_w && t > 0))) {
          moves[count++] = {nr, nc};
        }
      }
    }
  } else if (type == 2) { // Cavalier
    int dr[] = {-2,-2,-1,-1, 1, 1, 2, 2};
    int dc[] = {-1, 1,-2, 2,-2, 2,-1, 1};
    for (int i = 0; i < 8; i++) {
      int nr = r + dr[i], nc = c + dc[i];
      if (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
        int t = board[nr][nc];
        if (t == 0 || (is_w && t < 0) || (!is_w && t > 0)) {
          moves[count++] = {nr, nc};
        }
      }
    }
  } else if (type == 3 || type == 4 || type == 5) { // Fou, Tour, Reine
    int dirs[8][2];
    int num_dirs = 0;
    if (type == 3 || type == 5) {
      dirs[num_dirs][0] = -1; dirs[num_dirs++][1] = -1;
      dirs[num_dirs][0] = -1; dirs[num_dirs++][1] =  1;
      dirs[num_dirs][0] =  1; dirs[num_dirs++][1] = -1;
      dirs[num_dirs][0] =  1; dirs[num_dirs++][1] =  1;
    }
    if (type == 4 || type == 5) {
      dirs[num_dirs][0] = -1; dirs[num_dirs++][1] =  0;
      dirs[num_dirs][0] =  1; dirs[num_dirs++][1] =  0;
      dirs[num_dirs][0] =  0; dirs[num_dirs++][1] = -1;
      dirs[num_dirs][0] =  0; dirs[num_dirs++][1] =  1;
    }
    for (int i = 0; i < num_dirs; i++) {
      int nr = r + dirs[i][0], nc = c + dirs[i][1];
      while (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
        int t = board[nr][nc];
        if (t == 0) {
          moves[count++] = {nr, nc};
        } else {
          if ((is_w && t < 0) || (!is_w && t > 0)) {
            moves[count++] = {nr, nc};
          }
          break;
        }
        nr += dirs[i][0];
        nc += dirs[i][1];
      }
    }
  } else if (type == 6) { // Roi
    for (int dr = -1; dr <= 1; dr++) {
      for (int dc = -1; dc <= 1; dc++) {
        if (dr == 0 && dc == 0) continue;
        int nr = r + dr, nc = c + dc;
        if (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
          int t = board[nr][nc];
          if (t == 0 || (is_w && t < 0) || (!is_w && t > 0)) {
            moves[count++] = {nr, nc};
          }
        }
      }
    }
  }
  return count;
}

int eval_board() {
  int score = 0;
  for (int r = 0; r < 8; r++) {
    for (int c = 0; c < 8; c++) {
      int p = board[r][c];
      if (p != 0) {
        int val = VALS[abs_val(p)];
        int bonus = P_BONUS[r][c];
        if (p > 0) score += (val + bonus);
        else score -= (val + bonus);
      }
    }
  }
  return score;
}

struct FullMove { int r1, c1, r2, c2; };

FullMove bot_move() {
  FullMove best_moves[100];
  int best_count = 0;
  int best_score = 99999;

  Pos moves[30];
  for (int r = 0; r < 8; r++) {
    for (int c = 0; c < 8; c++) {
      if (board[r][c] < 0) {
        int count = get_moves(r, c, moves);
        for (int i = 0; i < count; i++) {
          int r2 = moves[i].r, c2 = moves[i].c;
          int p1 = board[r][c], p2 = board[r2][c2];

          board[r2][c2] = p1; board[r][c] = 0;
          int score = eval_board();
          board[r][c] = p1; board[r2][c2] = p2;

          if (score < best_score) {
            best_score = score;
            best_moves[0] = {r, c, r2, c2};
            best_count = 1;
          } else if (score == best_score && best_count < 100) {
            best_moves[best_count++] = {r, c, r2, c2};
          }
        }
      }
    }
  }
  if (best_count > 0) {
    return best_moves[rand() % best_count];
  }
  return {-1, -1, -1, -1};
}

void draw_sq(int r, int c, Pos cur, Pos sel, Pos moves[], int move_count) {
  int x = OX + c * SQ;
  int y = OY + r * SQ;

  Display::Color bg = ((r + c) % 2 == 0) ? C_LIGHT : C_DARK;

  if (sel.r == r && sel.c == c) bg = C_SEL;
  else if (cur.r == r && cur.c == c) bg = C_CUR;
  else {
    for (int i = 0; i < move_count; i++) {
      if (moves[i].r == r && moves[i].c == c) {
        bg = C_MOVE;
        break;
      }
    }
  }

  Display::pushRectUniform(Display::Rect(x, y, SQ, SQ), bg);

  int p = board[r][c];
  if (p != 0) {
    Display::Color fg = (p < 0) ? C_WHITE : C_BLACK;
    const char* sym = SYMBOLS[abs_val(p)];
    Display::drawString(sym, Point(x + 8, y + 3), false, fg, bg);
  }
}

void draw_all(Pos cur, Pos sel, Pos moves[], int move_count) {
  for (int r = 0; r < 8; r++) {
    for (int c = 0; c < 8; c++) {
      draw_sq(r, c, cur, sel, moves, move_count);
    }
  }
}

bool check_king(bool white_king) {
  int target = white_king ? 6 : -6;
  for (int r = 0; r < 8; r++)
    for (int c = 0; c < 8; c++)
      if (board[r][c] == target) return true;
  return false;
}

extern "C" void eadk_main() {
  Display::pushRectUniform(Display::Rect(0, 0, 320, 240), C_BG);
  Display::drawString("ECHECS NUMWORKS C++", Point(70, 40), true, C_WHITE, C_BG);
  Display::drawString("1 : Joueur vs Joueur", Point(60, 110), false, C_WHITE, C_BG);
  Display::drawString("2 : Joueur vs BOT (IA)", Point(60, 140), false, C_WHITE, C_BG);

  bool vs_bot = false;
  while (true) {
    Keyboard::State kbd = Keyboard::scan();
    if (kbd.keyDown(Keyboard::Key::One)) { vs_bot = false; break; }
    if (kbd.keyDown(Keyboard::Key::Two)) { vs_bot = true; break; }
    Timing::msleep(50);
  }

  init_board();
  Pos cur = {6, 4};
  Pos sel = {-1, -1};
  Pos moves[30];
  int move_count = 0;
  bool turn_white = true;

  Display::pushRectUniform(Display::Rect(0, 0, 320, 240), C_BG);
  draw_all(cur, sel, moves, move_count);

  while (true) {
    if (turn_white) {
      Display::drawString("Tour: BLANCS   ", Point(90, 4), false, C_WHITE, C_BG);
    } else {
      Display::drawString(vs_bot ? "Tour: BOT...  " : "Tour: NOIRS   ", Point(90, 4), false, C_WHITE, C_BG);
    }
    Display::drawString("OK: Select | Back: Annuler", Point(30, 220), false, Display::Color(0x9CF3), C_BG);

    if (vs_bot && !turn_white) {
      Timing::msleep(200);
      FullMove m = bot_move();
      if (m.r1 != -1) {
        int p = board[m.r1][m.c1];
        if (p == -1 && m.r2 == 7) p = -5; // Promotion Reine
        board[m.r2][m.c2] = p;
        board[m.r1][m.c1] = 0;
      }
      turn_white = true;
      draw_all(cur, {-1, -1}, moves, 0);

      if (!check_king(true)) {
        Display::drawString("VICTOIRE DU BOT !", Point(80, 4), false, C_RED, C_BG);
        break;
      }
      continue;
    }

    Keyboard::State kbd = Keyboard::scan();
    Pos old_cur = cur;
    bool key_pressed = false;

    if (kbd.keyDown(Keyboard::Key::Up) && cur.r > 0) { cur.r--; key_pressed = true; }
    else if (kbd.keyDown(Keyboard::Key::Down) && cur.r < 7) { cur.r++; key_pressed = true; }
    else if (kbd.keyDown(Keyboard::Key::Left) && cur.c > 0) { cur.c--; key_pressed = true; }
    else if (kbd.keyDown(Keyboard::Key::Right) && cur.c < 7) { cur.c++; key_pressed = true; }
    else if (kbd.keyDown(Keyboard::Key::Back)) {
      sel = {-1, -1};
      move_count = 0;
      draw_all(cur, sel, moves, move_count);
      key_pressed = true;
    }
    else if (kbd.keyDown(Keyboard::Key::OK)) {
      if (sel.r == -1) {
        int p = board[cur.r][cur.c];
        if ((turn_white && p > 0) || (!turn_white && p < 0)) {
          sel = cur;
          move_count = get_moves(cur.r, cur.c, moves);
        }
      } else {
        bool valid_move = false;
        for (int i = 0; i < move_count; i++) {
          if (moves[i].r == cur.r && moves[i].c == cur.c) {
            valid_move = true;
            break;
          }
        }
        if (valid_move) {
          int p = board[sel.r][sel.c];
          if (p == 1 && cur.r == 0) p = 5;
          if (p == -1 && cur.r == 7) p = -5;

          board[cur.r][cur.c] = p;
          board[sel.r][sel.c] = 0;

          turn_white = !turn_white;
          sel = {-1, -1};
          move_count = 0;

          if (!check_king(turn_white)) {
            Display::drawString(turn_white ? "VICTOIRE NOIRS !" : "VICTOIRE BLANCS !", Point(70, 4), false, Display::Color(0x07E0), C_BG);
            draw_all(cur, sel, moves, move_count);
            break;
          }
        } else {
          sel = {-1, -1};
          move_count = 0;
        }
      }
      key_pressed = true;
    }

    if (key_pressed) {
      draw_sq(old_cur.r, old_cur.c, cur, sel, moves, move_count);
      draw_sq(cur.r, cur.c, cur, sel, moves, move_count);
      if (sel.r != -1) {
        for (int i = 0; i < move_count; i++) {
          draw_sq(moves[i].r, moves[i].c, cur, sel, moves, move_count);
        }
      }
      Timing::msleep(150); // Anti-rebond
    }
    Timing::msleep(20);
  }
}
