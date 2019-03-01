#include<stdio.h>
#include<stdlib.h>

#define MAXINDEX (1 << 10)
#define BARSLEN  (MAXINDEX << 1)

 /* nat: type of numbers of bars with the same height */
typedef int nat;

// #define DEBUG 

struct _expr {
  nat bars[BARSLEN];
  int from, upto;
};

typedef struct _expr* expr;

/* initialize as expr {0,0,...,0,1} corresponding monomial [bar] */
void init_expr(expr e, int bar){
  for(int i=0;i<BARSLEN;++i) e->bars[i] = 0;
  e->from = 0;
  e->upto = bar;
  e->bars[bar] = 1;
  return;
}

void copy_expr(expr e_src, expr e_tgt){
  e_tgt->from = 0;
  e_tgt->upto = e_src->upto - e_src->from;
  int i;
  /* copying the meaningful contents */
  for(i=0;i<=e_tgt->upto;++i) e_tgt->bars[i] = e_src->bars[e_src->from+i];
  /* cleaning the remainder */
  for(;i<BARSLEN;++i) e_tgt->bars[i] = 0;
  return;
}

void print_expr(expr e){
  printf("(");
  for(int i=e->from;i<e->upto;++i) printf("%d,",(int)e->bars[i]);
  printf("%d)",(int)e->bars[e->upto]);
  return;
}

void print_poly(expr e){
  int h = e->upto - e->from;
  for(int j=e->bars[e->upto];j>1;--j) printf("%d.",h);
  printf("%d",h);
  for(int i=e->upto-1;i>=e->from;--i) {
    h = i - e->from; 
    for(int j=e->bars[i];j>0;--j) printf(".%d",h);
  }
  return;
}

int eq_expr(expr e1, expr e2){
  int i = e1->upto-e1->from;
  if(i == e2->upto-e2->from){
    for(;i>=0;--i)
      if(e1->bars[e1->from+i]!=e2->bars[e2->from+i])
        return 0;
    return 1;
  }
  return 0;
}

/* insertion of many bars (not used the monomial case) */
void insert_bars(expr e, int bar, int num){
  if(num){
    if(e->from == MAXINDEX){
      for(int i=e->upto-e->from;i>=0;--i){
        e->bars[i] = e->bars[e->from+i];
        e->bars[e->from+i] = 0;
      }
      e->upto -= e->from;
      e->from = 0;
    }
    bar += e->from;
    int i=e->from;
    while(i<bar){
      bar += e->bars[i];
      ++i;
    }
    e->bars[i] += num;
    if(e->upto<i) e->upto = i;
  }
  return;
}

/* insertion of a single bar */
void insert_one(expr e, int bar){
  if(e->from == MAXINDEX){
    if(e->upto >= BARSLEN) {
      fprintf(stderr,
              "The highest level becomes more than %d.",BARSLEN-MAXINDEX-1);
      exit(1);
    }
    for(int i=e->upto-e->from;i>=0;--i){
      e->bars[i] = e->bars[e->from+i];
      e->bars[e->from+i] = 0;
    }
    e->upto -= e->from;
    e->from = 0;
  }
  bar += e->from;
  int i=e->from;
  while(i<bar){
    bar += e->bars[i];
    ++i;
  }
  ++e->bars[i];
  if(e->upto<i) e->upto = i;
  return;
}

void apply_mono(expr e, int bar){
  bar += e->bars[e->from];
  e->bars[e->from] = 0;
  ++e->from;
  insert_one(e, bar);
  return;
}

void display(long i, expr e){
  printf("%3ld => ", i); print_poly(e); printf("\n");
  /* printf(" internal expr: "); print_expr(e); printf("\n"); */
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
  while(!eq_expr(e,e_tmp)){
    /* e_tmp: expr at the last power of 2 */
    /* e:     expr at i                   */
    #ifdef DEBUG
      display(i, e);
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
    for(i=1;i<=*cycle;++i) apply_mono(e_tmp, bar);
  } else
    for(i=pow;i<=*cycle;++i) apply_mono(e_tmp, bar);
  /* e_tmp: expr at *cycle+1 */

  /* - (2) finding the entry point by shifting two expressions */
  init_expr(e, bar);
  i = 1;
  while(!eq_expr(e,e_tmp)){
    #ifdef DEBUG
      display(i,e);
      display(i+*cycle,e_tmp);
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
  fprintf(stderr,"Usage: %s N\n", argv[0]); 
  exit(1);
}

int main(int argc, char *argv[]){
  int bar;
  long entry, cycle;
  if(argc<2) usage(argv);
  else bar = atoi(argv[1]);

  find_rho(bar,&entry,&cycle);
  return 0;
}
