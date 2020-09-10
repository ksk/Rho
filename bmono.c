#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>
#include<time.h>

#define BBITS 10
#define BSIZE (1 << BBITS)
#define IMASK (BSIZE-1) /* index mask for circular array */
#define nth(e,n) e->bars[(e->ofs+n)&IMASK]

#define SAVEFREQ (1 << 20) - 1
#define SAVEFILE "bmono.log"
#define LASTFILE "bmono.tmp"
#define SAVEMODE

clock_t start;
double passed; /* passed time (sec) */

int resume; /* use the log file if resume > 0 */

void abortf(const char *format, ...){
  va_list ap;
  va_start(ap, format);
  vfprintf(stderr, format, ap);
  va_end(ap);
  exit(1);
}

/* nat: type of numbers of bars with the same height */
typedef int nat;

/* #define DEBUG */

struct _expr {
  nat bars[BSIZE];
  int ofs, max;
  /* ofs : offset */
  /* max : highest level of decreasing polynomial,
           so (max + 1) is the length of the active area */
};

typedef struct _expr* expr;

/* initialize as expr {0,0,...,0,1} corresponding monomial [bar] */
void init_expr(expr e, int bar){
  int i;
  for(i=0;i<BSIZE;++i) e->bars[i] = 0;
  e->ofs = 0;
  e->max = bar;
  e->bars[bar] = 1;
  return;
}

void copy_expr(expr src, expr tgt){
  tgt->ofs = 0;
  tgt->max = src->max;
  int i;
  /* copying the meaningful contents */
  for(i=0;i<=tgt->max;++i)
    tgt->bars[i] = nth(src,i);
  /* cleaning the remainder */
  for(;i<BSIZE;++i) tgt->bars[i] = 0;
  return;
}

void print_expr(expr e){
  int i;
  printf("(");
  for(i=0;i<e->max;++i) printf("%d,",(int)nth(e,i));
  printf("%d)[%d,%d]",(int)nth(e,e->max),e->ofs,e->max);
  return;
}

void print_full_expr(expr e){
  int i;
  printf("[%d",e->bars[0]);
  for(i=1;i<BSIZE;++i) printf(",%d",e->bars[i]);
  printf("][%d,%d]\n",e->ofs,e->max);
  return;
}

void print_poly(expr e){
  int j, h = e->max;
  for(j=nth(e,h);j>1;--j) printf("%d.",h);
  printf("%d",h);
  --h;
  for(;h>=0;--h)
    for(j=nth(e,h);j>0;--j) printf(".%d",h);
  return;
}

int eq_expr(expr e1, expr e2){
  int h = e1->max;
  if(h!=e2->max) return 0;
  for(;h>=0;--h) if(nth(e1,h)!=nth(e2,h)) return 0;
  return 1;
}

/* insertion of a single bar */
void insert_one(expr e, int bar){
  int i = 0;
  while(i<bar){
    bar += nth(e,i);
    ++i;
  }
  ++nth(e,i);
  if(e->max<i) {
    e->max = i;
    if(BSIZE<=i) abortf("The highest level is beyond %d.\n",BSIZE-1);
  }
  return;
}

void apply_mono(expr e, int bar){
  bar += e->bars[e->ofs];
  e->bars[e->ofs] = 0;
  e->ofs = (e->ofs+1)&IMASK;
  --e->max;
  insert_one(e, bar);
  return;
}

void display(long i, expr e){
  printf("%3ld => ", i); print_poly(e); printf("\n");
  return;
}

void fputs_expr(FILE*fp, expr e){
  fwrite(e->bars, sizeof(nat), BSIZE, fp);
  fprintf(fp,",%d,%d", e->ofs, e->max);
  return;
}

void fgets_expr(FILE*fp, expr*e){
  fread((*e)->bars, sizeof(nat), BSIZE, fp);
  fscanf(fp,",%d,%d", &(*e)->ofs, &(*e)->max);
  return;
}

/* Save a log file for find_rho */
void find_rho_save(long i, long pow, expr e, expr e_tmp){
/*  printf("saved:\n"); display(i,e); display(pow,e_tmp); */
  FILE *fp = fopen(SAVEFILE, "w");
  if(fp==NULL) abortf("find_rho_save failed.\n");
  fwrite(&i, sizeof(long), 1, fp);
  fwrite(&pow, sizeof(long), 1, fp);
  /* fprintf(fp, "%ld,%ld:",i,pow); */
  fputs_expr(fp, e);
  fputs_expr(fp, e_tmp);
  double p = passed + (double)(clock()-start)/CLOCKS_PER_SEC;
  fwrite(&p, sizeof(double), 1, fp);
  fclose(fp);
  return;
}

void find_rho_load(long*_i, long*_pow, expr*_e, expr*_e_tmp){
  FILE *fp = fopen(SAVEFILE, "r");
  if(fp==NULL) abortf("find_rho_load failed.\n");
  fread(_i, sizeof(long), 1, fp);
  fread(_pow, sizeof(long), 1, fp);
  /* fscanf(fp, "%ld,%ld:",_i,_pow); */
  fgets_expr(fp, _e);
  fgets_expr(fp, _e_tmp);
  fread(&passed, sizeof(double), 1, fp);
  fclose(fp);
  /* display status */
  printf("Resuming from\n");
  display(*_i,*_e);
  if(*_pow)
    printf("in finding-cycle mode.\n");
  else
    printf("in finding-entry mode.\n");
  printf("%.2f sec passed.\n", passed);
  return;
}

void find_rho(int bar, long *entry, long *cycle){
  long i=2, pow=2;
  expr e = (expr)malloc(sizeof(struct _expr));
  init_expr(e, bar);
  expr e_tmp = (expr)malloc(sizeof(struct _expr));
  init_expr(e_tmp, bar);

  /* loop detection */
  display(1, e);
  apply_mono(e, bar);
  if(resume) find_rho_load(&i, &pow, &e, &e_tmp);
  if(pow==0) goto find_entry;
  while(!eq_expr(e,e_tmp)){
    /* e_tmp: expr at the last power of 2 */
    /* e:     expr at i                   */
    #ifdef DEBUG
      display(i, e);
    #endif
    #ifdef SAVEMODE
      if(!(i&SAVEFREQ)) find_rho_save(i, pow, e, e_tmp);
    #endif
    if(i==pow) {
      pow <<= 1;
      copy_expr(e,e_tmp);
    }
    apply_mono(e, bar);
    ++i;
  }
  #ifdef DEBUG
    display(i, e);
  #endif
  pow >>= 1;
  *cycle = i-pow;
  printf("Loop detected! (%ld = %ld [%ld])\n", i, pow, *cycle);
  
  /* finding the entry point */
  /* - (1) finding (*cycle+1)-th expression */
  if(*cycle < pow) { 
    init_expr(e_tmp,bar);
    i = 1;
  } else
    i = pow;
  for(;i<=*cycle;++i) apply_mono(e_tmp, bar);
  /* e_tmp: expr at *cycle+1 */

  /* - (2) finding the entry point by shifting two expressions */
  init_expr(e, bar);
  i = 1;
find_entry:
  while(!eq_expr(e,e_tmp)){
    #ifdef DEBUG
      display(i,e); display(i+*cycle,e_tmp);
    #endif
    #ifdef SAVEMODE
      if(!(i&SAVEFREQ)) find_rho_save(i, 0, e, e_tmp);
    #endif
    apply_mono(e, bar);
    apply_mono(e_tmp, bar);
    ++i;
  }
  *entry = i;
  printf("Loop entry found at %ld!\n", *entry);
  printf("Found! (%ld = %ld [%ld])\n", *entry+*cycle, *entry, *cycle);
  display(i, e);
  free(e); free(e_tmp);
  return;
}

void usage(char *argv[]){
  abortf("Usage: %s N [-]\n  - forces the resume mode.", argv[0]);
}

int main(int argc, char *argv[]){
  int bar;
  long entry, cycle;
  start = clock();
  passed = 0;
  resume = 0;
  
  if(argc<2) usage(argv);
  else {
    bar = atoi(argv[1]);
    if(argc >= 3) resume = 1;
  }

  find_rho(bar,&entry,&cycle);

  printf("CPU time: %.2f sec\n",
         passed + (double)(clock()-start)/CLOCKS_PER_SEC);
  return 0;
}
