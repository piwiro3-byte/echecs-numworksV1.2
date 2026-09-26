#include "eadkpp.h"
#include "palette.h"

extern const char eadk_app_name[] __attribute__((section(".rodata.eadk_app_name"))) = "Echecs";
extern const uint32_t eadk_api_level __attribute__((section(".rodata.eadk_api_level"))) = 0;

#include <cstdint>
#include <cstring>
#include <cstdlib>
#include <cstdio>

using namespace EADK;

// =====================================================================
// 0. SAUVEGARDE (limite expliquee dans la conversation : l'API
//    officielle EADK ne permet pas d'ecrire un fichier qui survit a
//    une extinction complete de la calculatrice. Ici, la sauvegarde
//    fonctionne tant que l'appli reste chargee en memoire, et propose
//    "reprendre / nouvelle partie" a chaque lancement.)
// =====================================================================
namespace Save {
  struct Blob {
    int8_t board[8][8];
    int8_t turn;
    uint8_t castling;
    int8_t epR, epC;
    uint16_t halfmove;
    uint8_t vsBot, botColor, elo;
    uint8_t magic;
  };
  static Blob s_ram;
  static bool s_hasRam = false;
  inline bool write(const Blob &b) { s_ram = b; s_hasRam = true; return true; }
  inline bool read(Blob &out) { if (s_hasRam) { out = s_ram; return true; } return false; }
  inline void erase() { s_hasRam = false; }
}

// =====================================================================
// 1. SPRITES DES PIECES -- portage EXACT du systeme du script Python
//    d'origine (chaines SS compressees -> rectangles empiles)
// =====================================================================
static const char* SS[6] = {
  "+%'$*&)$)'+&**)$++'%(--%+/'$*0)%)2+$(3-$'4/$&51$%63$",
  ",$%$+%'$)&*$(',$'(.$&)0$%*1$%+$$'+0$$,&$),/$*-.$#-'%*./$#/&$+/.$$0%$,0-$-1,$,2-$+3/$)41$(52$'63$",
  "+$'%*&)$)'($/'%$((($.('$()'$-)($(*-%),+$*-)$+.'$'//%*1)$)2+$(3-$&41$%53$$65$",
  "%%''+%''1%''%)3$&*1$'+/*&21$%33%$55%",
  "#$%%+$'%5$%%$&$$+&$$.&$$5&$$$'%$'$%'*'%$.'%$1$%'4'%$$(5$%)3%&+1$',/%(.-$'//%(1-$'2/$&31$%43$$55%",
  ",$%%*&)%,(%%)*+$'+/$&,1$%-3&&01$'1/%&31$%43$$55%"
};
struct SpriteSet { uint32_t rects[24]; int count; };
static SpriteSet SPR[7]; // index 1=pion 2=cavalier 3=fou 4=tour 5=dame 6=roi

static void buildSprites() {
  for (int n=0;n<6;n++) {
    const char* s = SS[n];
    int len = (int)strlen(s);
    SpriteSet &sp = SPR[n+1];
    sp.count = 0;
    for (int i=0; i+3<len && sp.count<24; i+=4) {
      uint32_t a=(uint8_t)s[i]-35, b=(uint8_t)s[i+1]-35, c=(uint8_t)s[i+2]-35, d=(uint8_t)s[i+3]-35;
      sp.rects[sp.count++] = a | (b<<5) | (c<<10) | (d<<15);
    }
  }
}
static void drawPiece(int p, int x, int y) {
  if (!p) return;
  int a = (p<0) ? -p : p;
  const SpriteSet &sp = SPR[a];
  Color oc = (p>0) ? Black : White;
  Color fc = (p>0) ? White : Color(0x141414);
  for (int i=0;i<sp.count;i++) {
    uint32_t v = sp.rects[i];
    int ox=(v&31), oy=((v>>5)&31), ow=((v>>10)&31)+2, oh=((v>>15)&31)+2;
    Display::pushRectUniform(Rect(x+ox+2, y+oy+2, ow, oh), oc);
  }
  for (int i=0;i<sp.count;i++) {
    uint32_t v = sp.rects[i];
    int ox=(v&31), oy=((v>>5)&31), fw=((v>>10)&31), fh=((v>>15)&31);
    if (fw>0 && fh>0) Display::pushRectUniform(Rect(x+ox+3, y+oy+3, fw, fh), fc);
  }
}

// =====================================================================
// 2. PLATEAU ET ETAT DE PARTIE
// =====================================================================
static int8_t bd[8][8];
static int turn;
static bool wKm, wRaM, wRhM, bKm, bRaM, bRhM;
static int epR, epC;
static int halfmove;

static bool vsBot = true;
static int  pcol  = 1;
static int  elo   = 500;

static bool chk = false, mate = false, isDraw = false;
static char drawReason[16] = "";

struct Move { int8_t fr, fc, tr, tc; };

static const int KN[8][2] = {{-2,-1},{-2,1},{-1,-2},{-1,2},{1,-2},{1,2},{2,-1},{2,1}};
static const int D8[8][2] = {{-1,-1},{-1,1},{1,-1},{1,1},{-1,0},{1,0},{0,-1},{0,1}};

static inline bool inb(int r,int c){ return r>=0 && r<8 && c>=0 && c<8; }
static inline int iabs(int x){ return x<0?-x:x; }

static void findKing(int color, int &kr, int &kc) {
  for (int r=0;r<8;r++) for (int c=0;c<8;c++) if (bd[r][c]==6*color){ kr=r; kc=c; return; }
  kr=-1; kc=-1;
}

static bool attacked(int r,int c,int attacker) {
  int pr = r + attacker;
  if (pr>=0 && pr<8) {
    for (int dc=-1; dc<=1; dc+=2) {
      int pc=c+dc;
      if (pc>=0 && pc<8 && bd[pr][pc]==attacker) return true;
    }
  }
  for (auto &k : KN) { int rr=r+k[0], cc=c+k[1]; if (inb(rr,cc) && bd[rr][cc]==2*attacker) return true; }
  for (int i=0;i<8;i++) {
    int dr=D8[i][0], dc=D8[i][1];
    int cr=r+dr, cc=c+dc;
    if (inb(cr,cc) && bd[cr][cc]==6*attacker) return true;
    while (inb(cr,cc)) {
      int p = bd[cr][cc];
      if (p) {
        int wanted = (i<4) ? 3 : 4;
        if (p==5*attacker || p==wanted*attacker) return true;
        break;
      }
      cr+=dr; cc+=dc;
    }
  }
  return false;
}
static inline bool isInCheck(int color) {
  int kr,kc; findKing(color,kr,kc);
  return kr>=0 && attacked(kr,kc,-color);
}

static int genPseudo(int r,int c, Move *out, bool capturesOnly) {
  int n=0;
  int p = bd[r][c];
  int col = (p>0)?1:-1;
  int pt = (p<0)?-p:p;
  if (pt==1) {
    int f = -col;
    if (!capturesOnly && bd[r+f][c]==0) {
      out[n++] = {(int8_t)r,(int8_t)c,(int8_t)(r+f),(int8_t)c};
      int startRow = (col==1)?6:1;
      if (r==startRow && bd[r+2*f][c]==0) out[n++] = {(int8_t)r,(int8_t)c,(int8_t)(r+2*f),(int8_t)c};
    }
    for (int dc=-1; dc<=1; dc+=2) {
      int tc=c+dc;
      if (tc<0||tc>7) continue;
      bool isEp = (r+f==epR && tc==epC);
      if (bd[r+f][tc]*col<0 || isEp) out[n++] = {(int8_t)r,(int8_t)c,(int8_t)(r+f),(int8_t)tc};
    }
    return n;
  }
  const int (*dirs)[2] = (pt==2)?KN : (pt==3)?D8 : (pt==4)?D8+4 : D8;
  int cnt = (pt==2)?8 : (pt==3)?4 : (pt==4)?4 : 8;
  for (int i=0;i<cnt;i++) {
    int dr=dirs[i][0], dc=dirs[i][1];
    int cr=r+dr, cc=c+dc;
    while (inb(cr,cc)) {
      int tp = bd[cr][cc]*col;
      if (tp>0) break;
      if (tp<0 || !capturesOnly) out[n++] = {(int8_t)r,(int8_t)c,(int8_t)cr,(int8_t)cc};
      if (tp<0 || pt==2 || pt==6) break;
      cr+=dr; cc+=dc;
    }
  }
  if (!capturesOnly && pt==6) {
    int ro = (col==1)?7:0;
    if (r==ro && c==4 && !isInCheck(col)) {
      bool km  = (col==1)? wKm : bKm;
      bool raM = (col==1)? wRaM: bRaM;
      bool rhM = (col==1)? wRhM: bRhM;
      if (!km) {
        if (!rhM && bd[ro][7]==4*col && bd[ro][5]==0 && bd[ro][6]==0 &&
            !attacked(ro,5,-col) && !attacked(ro,6,-col))
          out[n++] = {(int8_t)r,(int8_t)c,(int8_t)ro,6};
        if (!raM && bd[ro][0]==4*col && bd[ro][1]==0 && bd[ro][2]==0 && bd[ro][3]==0 &&
            !attacked(ro,3,-col) && !attacked(ro,2,-col))
          out[n++] = {(int8_t)r,(int8_t)c,(int8_t)ro,2};
      }
    }
  }
  return n;
}

struct Undo { int8_t moved, captured; int8_t epR,epC; bool wKm,wRaM,wRhM,bKm,bRaM,bRhM; int halfmove; bool wasCastle, wasEp, wasPromo; int8_t rookFrom,rookTo; };

static Undo makeMove(const Move &m) {
  Undo u; u.epR=epR; u.epC=epC; u.wKm=wKm; u.wRaM=wRaM; u.wRhM=wRhM; u.bKm=bKm; u.bRaM=bRaM; u.bRhM=bRhM; u.halfmove=halfmove;
  u.wasCastle=u.wasEp=u.wasPromo=false;
  int8_t p = bd[m.fr][m.fc];
  int col = (p>0)?1:-1;
  int pt = (p<0)?-p:p;
  u.moved = p; u.captured = bd[m.tr][m.tc];

  halfmove = (pt==1 || u.captured!=0) ? 0 : halfmove+1;

  if (pt==1 && m.fc!=m.tc && bd[m.tr][m.tc]==0) {
    u.wasEp = true;
    u.captured = bd[m.fr][m.tc];
    bd[m.fr][m.tc] = 0;
  }
  if (pt==6 && iabs(m.fc-m.tc)==2) {
    u.wasCastle = true;
    int ro = m.fr;
    if (m.tc==6) { u.rookFrom=7; u.rookTo=5; bd[ro][5]=bd[ro][7]; bd[ro][7]=0; }
    else         { u.rookFrom=0; u.rookTo=3; bd[ro][3]=bd[ro][0]; bd[ro][0]=0; }
  }
  bd[m.tr][m.tc] = p; bd[m.fr][m.fc] = 0;
  if (pt==1 && (m.tr==0 || m.tr==7)) { u.wasPromo=true; bd[m.tr][m.tc] = 5*col; }

  epR = epC = -1;
  if (pt==1 && iabs(m.fr-m.tr)==2) { epR=(m.fr+m.tr)/2; epC=m.fc; }

  if (pt==6) { if (col==1) wKm=true; else bKm=true; }
  if (pt==4) {
    if (m.fr==7 && m.fc==0) wRaM=true;
    if (m.fr==7 && m.fc==7) wRhM=true;
    if (m.fr==0 && m.fc==0) bRaM=true;
    if (m.fr==0 && m.fc==7) bRhM=true;
  }
  if (m.tr==7 && m.tc==0) wRaM=true;
  if (m.tr==7 && m.tc==7) wRhM=true;
  if (m.tr==0 && m.tc==0) bRaM=true;
  if (m.tr==0 && m.tc==7) bRhM=true;

  turn = -turn;
  return u;
}
static void unmakeMove(const Move &m, const Undo &u) {
  turn = -turn;
  bd[m.fr][m.fc] = u.moved;
  bd[m.tr][m.tc] = u.wasEp ? 0 : u.captured;
  if (u.wasEp) bd[m.fr][m.tc] = u.captured;
  if (u.wasCastle) {
    int ro=m.fr;
    bd[ro][u.rookFrom] = bd[ro][u.rookTo];
    bd[ro][u.rookTo] = 0;
  }
  epR=u.epR; epC=u.epC; wKm=u.wKm; wRaM=u.wRaM; wRhM=u.wRhM; bKm=u.bKm; bRaM=u.bRaM; bRhM=u.bRhM; halfmove=u.halfmove;
}

static int genLegal(int r,int c, Move *out) {
  Move pm[28];
  int n = genPseudo(r,c,pm,false);
  int col = (bd[r][c]>0)?1:-1;
  int k=0;
  for (int i=0;i<n;i++) {
    Undo u = makeMove(pm[i]);
    if (!isInCheck(col)) out[k++] = pm[i];
    unmakeMove(pm[i],u);
  }
  return k;
}
static bool hasLegalMove(int color) {
  Move mv[28];
  for (int r=0;r<8;r++) for (int c=0;c<8;c++) if (bd[r][c]*color>0) if (genLegal(r,c,mv)>0) return true;
  return false;
}
static int genAllLegal(int color, Move *out) {
  Move mv[28]; int total=0;
  for (int r=0;r<8;r++) for (int c=0;c<8;c++) if (bd[r][c]*color>0) {
    int n = genLegal(r,c,mv);
    for (int i=0;i<n;i++) out[total++] = mv[i];
  }
  return total;
}

// =====================================================================
// 3. EVALUATION + IA (jusqu'a ~1000 elo, priorites explicites)
// =====================================================================
static const int VAL[7] = {0,100,320,330,500,900,0};

static const int8_t PST_P[64] = {
  0,0,0,0,0,0,0,0, 5,5,5,-5,-5,5,5,5, 1,1,2,4,4,2,1,1, 0,0,0,3,3,0,0,0,
  0,0,0,3,3,0,0,0, 1,-1,-2,0,0,-2,-1,1, 1,2,2,-3,-3,2,2,1, 0,0,0,0,0,0,0,0
};
static const int8_t PST_N[64] = {
  -5,-4,-3,-3,-3,-3,-4,-5, -4,-2,0,0,0,0,-2,-4, -3,0,1,2,2,1,0,-3, -3,0,2,3,3,2,0,-3,
  -3,0,2,3,3,2,0,-3, -3,0,1,2,2,1,0,-3, -4,-2,0,0,0,0,-2,-4, -5,-4,-3,-3,-3,-3,-4,-5
};
static const int8_t PST_B[64] = {
  -2,-1,-1,-1,-1,-1,-1,-2, -1,0,0,0,0,0,0,-1, -1,0,1,2,2,1,0,-1, -1,1,1,2,2,1,1,-1,
  -1,0,2,2,2,2,0,-1, -1,2,2,2,2,2,2,-1, -1,1,0,0,0,0,1,-1, -2,-1,-1,-1,-1,-1,-1,-2
};
static const int8_t PST_K_MID[64] = {
  2,3,1,0,0,1,3,2, 2,2,0,0,0,0,2,2, -1,-2,-2,-2,-2,-2,-2,-1, -2,-3,-3,-4,-4,-3,-3,-2,
  -2,-3,-3,-4,-4,-3,-3,-2, -1,-2,-2,-2,-2,-2,-2,-1, 2,2,0,0,0,0,2,2, 2,3,1,0,0,1,3,2
};
static const int8_t PST_K_END[64] = {
  -5,-3,-3,-3,-3,-3,-3,-5, -3,-1,0,0,0,0,-1,-3, -3,0,2,3,3,2,0,-3, -3,0,3,4,4,3,0,-3,
  -3,0,3,4,4,3,0,-3, -3,0,2,3,3,2,0,-3, -3,-1,0,0,0,0,-1,-3, -5,-3,-3,-3,-3,-3,-3,-5
};

static bool endgame() {
  int n=0; for (int r=0;r<8;r++) for (int c=0;c<8;c++) if (bd[r][c] && iabs(bd[r][c])!=6) n++;
  return n<7;
}
static int pstVal(int p,int r,int c) {
  int a = (p<0)?-p:p;
  int idx = (p>0) ? r*8+c : (7-r)*8+c;
  switch(a){
    case 1: return PST_P[idx];
    case 2: return PST_N[idx];
    case 3: return PST_B[idx];
    case 5: return (PST_B[idx]+PST_N[idx])/3;
    case 6: return endgame()?PST_K_END[idx]:PST_K_MID[idx];
    default: return 0;
  }
}
static int materialBalance() {
  int s=0; for (int r=0;r<8;r++) for (int c=0;c<8;c++) { int p=bd[r][c]; if(p) s += VAL[iabs(p)]*(p>0?1:-1); }
  return s;
}

static int quiesce(int color, int alpha, int beta, int depthLeft) {
  int standPat = color * materialBalance();
  if (standPat >= beta) return beta;
  if (standPat > alpha) alpha = standPat;
  if (depthLeft<=0) return alpha;
  for (int r=0;r<8;r++) for (int c=0;c<8;c++) if (bd[r][c]*color>0) {
    Move pm[28]; int n = genPseudo(r,c,pm,true);
    for (int i=0;i<n;i++) {
      Undo u = makeMove(pm[i]);
      if (!isInCheck(color)) {
        int v = -quiesce(-color,-beta,-alpha,depthLeft-1);
        unmakeMove(pm[i],u);
        if (v>=beta) return beta;
        if (v>alpha) alpha=v;
      } else unmakeMove(pm[i],u);
    }
  }
  return alpha;
}

static int negamax(int color, int depth, int alpha, int beta) {
  if (depth==0) return quiesce(color, alpha, beta, 2);
  Move mv[96]; int n = genAllLegal(color, mv);
  if (n==0) return isInCheck(color) ? -100000+depth : 0;
  int best = -999999;
  for (int i=0;i<n;i++) {
    Undo u = makeMove(mv[i]);
    int v = -negamax(-color, depth-1, -beta, -alpha);
    unmakeMove(mv[i],u);
    if (v>best) best=v;
    if (best>alpha) alpha=best;
    if (alpha>=beta) break;
  }
  return best;
}

static int moveHeuristic(const Move &m, int color) {
  int p = bd[m.fr][m.fc];
  int pt = (p<0)?-p:p;
  int cap = bd[m.tr][m.tc];
  int score = 0;
  bool isCastle = (pt==6 && iabs(m.fc-m.tc)==2);

  score += pstVal(p,m.tr,m.tc) - pstVal(p,m.fr,m.fc);

  if (cap) score += 1000 + 10*VAL[iabs(cap)] - VAL[pt];
  bool epCapture = (pt==1 && m.fc!=m.tc && cap==0);
  if (epCapture) score += 1000 + 10*VAL[1];

  if (pt==1 && (m.tr==0||m.tr==7)) score += 800;

  Undo u = makeMove(m);
  bool givesCheck = isInCheck(-color);
  bool oppHasMove = hasLegalMove(-color);
  unmakeMove(m,u);
  if (givesCheck && !oppHasMove) score += 100000;
  else if (givesCheck) score += 60;

  if (isCastle) score += 12;
  return score;
}

static void diffParams(int e, int &depth, int &noise) {
  if (e < 250)      { depth=1; noise=140; }
  else if (e < 450) { depth=2; noise=90;  }
  else if (e < 650) { depth=2; noise=55;  }
  else if (e < 850) { depth=3; noise=30;  }
  else              { depth=3; noise=10;  }
}

static Move chooseBotMove() {
  int depth, noise; diffParams(elo, depth, noise);
  Move mv[96]; int n = genAllLegal(turn, mv);
  int scores[96]; int best=-9999999;
  for (int i=0;i<n;i++) {
    int heur = moveHeuristic(mv[i], turn);
    Undo u = makeMove(mv[i]);
    int deep = -negamax(-turn, depth-1, -999999, 999999);
    unmakeMove(mv[i],u);
    scores[i] = deep*4 + heur;
    if (scores[i]>best) best=scores[i];
  }
  int pool[96], pn=0;
  for (int i=0;i<n;i++) if (scores[i] >= best-noise) pool[pn++]=i;
  uint32_t pick = EADK::random() % (uint32_t)pn;
  return mv[ pool[pick] ];
}

// =====================================================================
// 4. SAUVEGARDE : conversion vers/depuis Save::Blob
// =====================================================================
static void saveGame() {
  Save::Blob b{};
  memcpy(b.board, bd, sizeof(bd));
  b.turn = (int8_t)turn;
  b.castling = (wKm?1:0)|(wRaM?2:0)|(wRhM?4:0)|(bKm?8:0)|(bRaM?16:0)|(bRhM?32:0);
  b.epR=(int8_t)epR; b.epC=(int8_t)epC;
  b.halfmove=(uint16_t)halfmove;
  b.vsBot=vsBot; b.botColor=(uint8_t)(pcol<0?1:0); b.elo=(uint8_t)elo;
  b.magic=0xC5;
  Save::write(b);
}
static bool loadGame() {
  Save::Blob b;
  if (!Save::read(b) || b.magic!=0xC5) return false;
  memcpy(bd, b.board, sizeof(bd));
  turn=b.turn;
  wKm=b.castling&1; wRaM=b.castling&2; wRhM=b.castling&4; bKm=b.castling&8; bRaM=b.castling&16; bRhM=b.castling&32;
  epR=b.epR; epC=b.epC; halfmove=b.halfmove;
  vsBot=b.vsBot; pcol = b.botColor?-1:1; elo=b.elo;
  chk = isInCheck(turn);
  return true;
}
static void newGame() {
  static const int8_t R[8]={4,2,3,5,6,3,2,4};
  for (int c=0;c<8;c++){ bd[0][c]=-R[c]; bd[1][c]=-1; bd[6][c]=1; bd[7][c]=R[c]; }
  for (int r=2;r<6;r++) for(int c=0;c<8;c++) bd[r][c]=0;
  turn=1; epR=epC=-1; halfmove=0;
  wKm=wRaM=wRhM=bKm=bRaM=bRhM=false;
  chk=mate=isDraw=false; drawReason[0]=0;
  Save::erase();
}

// =====================================================================
// 5. AFFICHAGE DU PLATEAU
// =====================================================================
static const int SQ = 27, OX = 4, OY = 4;
static int selR=-1, selC=-1, curR=6, curC=4;
static Move legalCache[28]; static int legalCount=0;

static void drawSquare(int r,int c) {
  int x = OX + c*SQ, y = OY + r*SQ;
  bool dark = ((r+c)%2)==1;
  Color bg = dark ? Color(0x647082) : Color(0xE1E1E6);
  int p = bd[r][c];
  if (p==6*turn && chk) bg = Red;
  else if (r==selR && c==selC) bg = Green;
  else {
    for (int i=0;i<legalCount;i++) if (legalCache[i].tr==r && legalCache[i].tc==c) { bg = Orange; break; }
  }
  Display::pushRectUniform(Rect(x,y,SQ,SQ), bg);
  if (r==curR && c==curC) {
    Color gold(0xFFD700);
    Display::pushRectUniform(Rect(x,y,SQ,2),gold);
    Display::pushRectUniform(Rect(x,y+SQ-2,SQ,2),gold);
    Display::pushRectUniform(Rect(x,y,2,SQ),gold);
    Display::pushRectUniform(Rect(x+SQ-2,y,2,SQ),gold);
  }
  drawPiece(p, x, y);
}
static void drawBoard() {
  for (int r=0;r<8;r++) for (int c=0;c<8;c++) drawSquare(r,c);
}
static void drawPanel() {
  Display::pushRectUniform(Rect(228,0,92,240), Color(0x0F141C));
  Display::drawString(turn==1?"BLANCS":"NOIRS", Point(234,44), true, White, Color(0x0F141C));
  const char *msg = mate ? "MAT !" : (isDraw ? drawReason : (chk ? "ECHEC !" : ""));
  Display::drawString(msg, Point(234,100), true, Red, Color(0x0F141C));
  Display::drawString("OK: jouer", Point(234,190), false, Color(0x8296AA), Color(0x0F141C));
}
static void redraw() { drawPanel(); drawBoard(); }

// =====================================================================
// 6. ECRAN DE MENU (Mode / Joueur / Elo / Jouer)
// =====================================================================
static void waitAllKeysReleased() {
  while (true) {
    Keyboard::State kbd = Keyboard::scan();
    bool any = kbd.keyDown(Keyboard::Key::Up) || kbd.keyDown(Keyboard::Key::Down) ||
               kbd.keyDown(Keyboard::Key::Left) || kbd.keyDown(Keyboard::Key::Right) ||
               kbd.keyDown(Keyboard::Key::OK) || kbd.keyDown(Keyboard::Key::EXE);
    if (!any) return;
    Timing::msleep(15);
  }
}

static void runMenu() {
  int cur = 0;
  const char *labels[4] = {"Mode","Joueur","Elo","Jouer"};
  while (true) {
    Display::pushRectUniform(Rect(0,0,320,240), Color(0x0F141C));
    Display::drawString("PARAMETRES", Point(108,10), true, Color(0xFFD700), Color(0x0F141C));
    for (int i=0;i<4;i++) {
      int y=50+i*40;
      Color rowBg = (i==cur) ? Color(0x28415F) : Color(0x18202C);
      Display::pushRectUniform(Rect(20,y,280,34), rowBg);
      Display::drawString(labels[i], Point(34,y+8), false, (i==cur)?Color(0xFFD700):Color(0x8296AA), rowBg);
      char shown[40];
      if (i==0) snprintf(shown,sizeof(shown), (i==cur)?"< %s >":"%s", vsBot? "VS BOT":"1 VS 1");
      else if (i==1) snprintf(shown,sizeof(shown), (i==cur)?"< %s >":"%s", (pcol<0)? "NOIRS":"BLANCS");
      else if (i==2) snprintf(shown,sizeof(shown), (i==cur)?"< %d >":"%d", elo);
      else strcpy(shown, " ");
      Display::drawString(shown, Point(300-8*(int)strlen(shown), y+8), false, (i==cur)?White:Color(0x8296AA), rowBg);
    }
    Display::drawString("Haut/Bas: choisir   Gauche/Droite: changer", Point(15,220), false, Color(0x647082), Color(0x0F141C));

    Keyboard::State kbd;
    bool up,dn,lt,rt,ok;
    do {
      kbd = Keyboard::scan();
      up=kbd.keyDown(Keyboard::Key::Up); dn=kbd.keyDown(Keyboard::Key::Down);
      lt=kbd.keyDown(Keyboard::Key::Left); rt=kbd.keyDown(Keyboard::Key::Right);
      ok=kbd.keyDown(Keyboard::Key::OK) || kbd.keyDown(Keyboard::Key::EXE);
      Timing::msleep(15);
    } while (!(up||dn||lt||rt||ok));

    if (up) cur = (cur>0)?cur-1:0;
    else if (dn) cur = (cur<3)?cur+1:3;
    else if (lt || rt) {
      int dir = lt ? -1 : 1;
      if (cur==0) vsBot = !vsBot;
      else if (cur==1) pcol = -pcol;
      else if (cur==2) { elo += dir*100; if (elo<100) elo=100; if (elo>1000) elo=1000; }
    } else if (ok && cur==3) { waitAllKeysReleased(); return; }
    waitAllKeysReleased();
  }
}

// =====================================================================
// 7. BOUCLE DE JEU
// =====================================================================
static void applyMove(const Move &m) {
  makeMove(m);
  chk = isInCheck(turn);
  bool anyMove = hasLegalMove(turn);
  mate=false; isDraw=false; drawReason[0]=0;
  if (!anyMove) { if (chk) mate=true; else { isDraw=true; strcpy(drawReason,"PAT"); } }
  else if (halfmove>99) { isDraw=true; strcpy(drawReason,"50 COUPS"); }
  if (mate || isDraw) Save::erase(); else saveGame();
}

static bool askResume() {
  Display::pushRectUniform(Rect(0,0,320,240), Color(0x0F141C));
  Display::drawString("Une partie est en cours.", Point(20,80), false, White, Color(0x0F141C));
  Display::drawString("OK=reprendre  Backspace=nouvelle partie", Point(10,110), false, Color(0x8296AA), Color(0x0F141C));
  while (true) {
    Keyboard::State kbd = Keyboard::scan();
    if (kbd.keyDown(Keyboard::Key::OK) || kbd.keyDown(Keyboard::Key::EXE)) { waitAllKeysReleased(); return true; }
    if (kbd.keyDown(Keyboard::Key::Backspace)) { waitAllKeysReleased(); return false; }
    Timing::msleep(30);
  }
}

int main(int argc, char * argv[]) {
  buildSprites();

  bool haveSave = loadGame();
  bool resumed = haveSave && askResume();
  if (!resumed) { runMenu(); newGame(); }
  redraw();

  bool okPrev=false, bsPrev=false, upPrev=false, dnPrev=false, ltPrev=false, rtPrev=false;

  while (1) {
    if (mate || isDraw) { Timing::msleep(200); continue; }

    if (vsBot && turn!=pcol) {
      Move m = chooseBotMove();
      Timing::msleep(250 + elo/4);
      applyMove(m);
      selR=selC=-1; legalCount=0;
      redraw();
      continue;
    }

    Keyboard::State kbd = Keyboard::scan();
    bool up=kbd.keyDown(Keyboard::Key::Up), dn=kbd.keyDown(Keyboard::Key::Down);
    bool lt=kbd.keyDown(Keyboard::Key::Left), rt=kbd.keyDown(Keyboard::Key::Right);
    bool ok=kbd.keyDown(Keyboard::Key::OK) || kbd.keyDown(Keyboard::Key::EXE);
    bool bs=kbd.keyDown(Keyboard::Key::Backspace);

    int oR=curR, oC=curC;
    if (up && !upPrev) curR = (curR>0)?curR-1:0;
    if (dn && !dnPrev) curR = (curR<7)?curR+1:7;
    if (lt && !ltPrev) curC = (curC>0)?curC-1:0;
    if (rt && !rtPrev) curC = (curC<7)?curC+1:7;
    if (oR!=curR || oC!=curC) { drawSquare(oR,oC); drawSquare(curR,curC); }

    if (bs && !bsPrev) {
      int pr=selR, pc=selC; selR=selC=-1; int lc=legalCount; legalCount=0;
      if (pr>=0) drawSquare(pr,pc);
      for (int i=0;i<lc;i++) drawSquare(legalCache[i].tr,legalCache[i].tc);
    }
    if (ok && !okPrev) {
      if (bd[curR][curC]*turn>0) {
        int pr=selR, pc=selC; int lc=legalCount;
        selR=curR; selC=curC;
        legalCount = genLegal(curR,curC,legalCache);
        if (pr>=0) drawSquare(pr,pc);
        for (int i=0;i<lc;i++) drawSquare(legalCache[i].tr,legalCache[i].tc);
        drawSquare(selR,selC);
        for (int i=0;i<legalCount;i++) drawSquare(legalCache[i].tr,legalCache[i].tc);
      } else if (selR>=0) {
        bool canGo=false; for (int i=0;i<legalCount;i++) if (legalCache[i].tr==curR && legalCache[i].tc==curC) canGo=true;
        if (canGo) {
          Move m{(int8_t)selR,(int8_t)selC,(int8_t)curR,(int8_t)curC};
          selR=selC=-1; legalCount=0;
          applyMove(m);
          redraw();
        }
      }
    }
    okPrev=ok; bsPrev=bs; upPrev=up; dnPrev=dn; ltPrev=lt; rtPrev=rt;
    Timing::msleep(15);
  }
}
