#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <time.h>
#include <assert.h>
#include </home/simon/generalsllist.c> // Find @ https://github.com/FastAsChuff/Generic-Singly-Linked-List/blob/main/generalsllist.c

#define MIN(x,y) ((x)<(y) ? (x) : (y))
#define MANHATTEN_DIST(x1,y1,x2,y2) (abs((x1)-(x2)) + abs((y1)-(y2)))
#define ORDER_LESSTHAN(o1,o2) (((o1.visited) < (o2.visited)) \
  || (((o1.visited) == 0) && ((o1.Mval)<(o2.Mval))) \
  || (((o1.Mval)==(o2.Mval)) && ((o1.visited) == 0) && ((o1.Mdist) < (o2.Mdist))))

// gcc pathprob2.c -o pathprob2.bin -O3 -march=native -Wall 

typedef struct node {
  struct node *next; // Must be first member
  struct node *prev; 
  int16_t x;
  int16_t y;
} leastcostpathnode_t;

_Bool printleastcostpathhtml(leastcostpathnode_t leastcostpath, int16_t *a, int16_t m, int16_t n, char *filename) {
  FILE *fp = fopen(filename, "w");
  if (fp == NULL) return false;
  uint8_t *visited = calloc(m*n, sizeof(uint8_t));
  leastcostpathnode_t leastcostpathsaved = leastcostpath;
  int32_t x,y;
  while (1) {  
    visited[m*leastcostpath.y + leastcostpath.x] = 1;
    if (leastcostpath.next == NULL) break;
    leastcostpath = *leastcostpath.next;
  };
  leastcostpath = leastcostpathsaved;
  
  fprintf(fp, "<html>\n");
  fprintf(fp, "  <title>Least Cost Path</title>\n");
  fprintf(fp, "  <body>\n");
  fprintf(fp, "    <table cols=%i>\n", m);
  for (y=0; y<n; y++) {
    fprintf(fp, "      <tr>");
    for (x=0; x<m; x++) {
      if (visited[m*y + x]) {
        fprintf(fp, "<td><b>%i</b></td>", a[m*y + x]);
      } else {
        fprintf(fp, "<td>%i</td>", a[m*y + x]);
      }
    }
    fprintf(fp, "</tr>\n");
  }
  fprintf(fp, "    </table>\n");
  fprintf(fp, "  </body>\n");
  fprintf(fp, "</html>\n");
  free(visited);
  fclose(fp);
  return true;
}

void printleastcostpath(leastcostpathnode_t leastcostpath) {
  int32_t counter = 0;
  while (1) {  
    printf("[%i, %i] ", leastcostpath.x, leastcostpath.y);
    counter++;
    if (counter == 8) {
      counter = 0;
      printf("\n");
    }
    if (leastcostpath.next == NULL) break;
    leastcostpath = *leastcostpath.next;
  };
  printf("\n");
}


_Bool isinleastcostpath(leastcostpathnode_t leastcostpath, int16_t x, int16_t y) {
  while (1) {  
    if ((leastcostpath.x == x) && (leastcostpath.y == y)) return true;
    if (leastcostpath.next == NULL) return false;
    leastcostpath = *leastcostpath.next;
  }
}

_Bool findleastcostpath(
    leastcostpathnode_t **leastcostpathroot, 
    leastcostpathnode_t **leastcostpath, 
    int16_t E_x, 
    int16_t E_y, 
    int16_t S_x, 
    int16_t S_y, 
    int32_t *pathlen, 
    int32_t *M, 
    int16_t *a, 
    int16_t m, 
    int16_t n, 
    int32_t maxub) {
  int32_t i, up, down, left, right;
  int32_t pathlength = 1;
  int32_t pathcost = a[m*S_y + S_x];
  leastcostpathnode_t *leastcostpathprev = NULL;
  leastcostpathnode_t newnode;
  newnode.next = NULL;
  newnode.x = S_x;
  newnode.y = S_y;
  newnode.prev = NULL;
  appendnode((void **)leastcostpathroot, (void **)leastcostpath, (void *)&newnode, sizeof(newnode), alignof(newnode));
  uint8_t *visited = calloc(m*n, sizeof(uint8_t));
  if (visited == NULL) return false;
  visited[m*S_y + S_x] = 1;
  typedef struct {
    int32_t Mval;
    int32_t Mdist;
    int16_t x;
    int16_t y;
    int8_t visited;
  } order_t; 
  order_t order[4];
  order_t temp;
  _Bool sorted;
  int32_t requiredMval;
  while (((*leastcostpath)->x != E_x) || ((*leastcostpath)->y != E_y)) {
    if ((*leastcostpath)->x > 0) {
      left = M[(*leastcostpath)->y*m + (*leastcostpath)->x - 1];
    } else {
      left = maxub;
    }
    if (((*leastcostpath)->x+1) < m) {
      right = M[(*leastcostpath)->y*m + (*leastcostpath)->x + 1];
    } else {
      right = maxub;
    }
    if (((*leastcostpath)->y+1) < n) {
      down = M[((*leastcostpath)->y+1)*m + (*leastcostpath)->x];
    } else {
      down = maxub;
    }
    if ((*leastcostpath)->y > 0) {
      up = M[((*leastcostpath)->y-1)*m + (*leastcostpath)->x];
    } else {
      up = maxub;
    }
    order[0] = (order_t){.Mval = up, .x = (*leastcostpath)->x, .y = (*leastcostpath)->y - 1};
    order[1] = (order_t){.Mval = down, .x = (*leastcostpath)->x, .y = (*leastcostpath)->y + 1};
    order[2] = (order_t){.Mval = left, .x = (*leastcostpath)->x - 1, .y = (*leastcostpath)->y};
    order[3] = (order_t){.Mval = right, .x = (*leastcostpath)->x + 1, .y = (*leastcostpath)->y};
    for (i=0; i<4; i++) {
      if (order[i].Mval < maxub) {
        order[i].visited = visited[m*order[i].y + order[i].x];
        order[i].Mdist = MANHATTEN_DIST(E_x,E_y,order[i].x,order[i].y);
      } else {
        order[i].visited = 1;
        order[i].Mdist = m+n;
      }
    }
    sorted = false;
    while (!sorted) {
      sorted = true;
      for (i=1; i<4; i++) {
        if (ORDER_LESSTHAN(order[i],order[i-1])) {
          temp = order[i];
          order[i] = order[i-1];
          order[i-1] = temp;
          sorted = false;
        }
      }
    }
    requiredMval = M[(*leastcostpath)->y*m + (*leastcostpath)->x] - a[(*leastcostpath)->y*m + (*leastcostpath)->x];
    if ((order[0].visited == 0) && (order[0].Mval == requiredMval)) {
      newnode.x = order[0].x;
      newnode.y = order[0].y;
      newnode.prev = *leastcostpath;
      appendnode(NULL, (void **)leastcostpath, (void *)&newnode, sizeof(newnode), alignof(newnode));
      visited[m*order[0].y + order[0].x] = 1;
      pathlength++;
      pathcost += a[m*(*leastcostpath)->y + (*leastcostpath)->x];
      //printf("[%i, %i] ", (*leastcostpath)->x, (*leastcostpath)->y);
    } else {
      //printf("<%i, %i> ", (*leastcostpath)->x, (*leastcostpath)->y);
      leastcostpathprev = (*leastcostpath)->prev;
      pathcost -= a[m*(*leastcostpath)->y + (*leastcostpath)->x];
      free(*leastcostpath);
      pathlength--;
      *leastcostpath = leastcostpathprev;
      (*leastcostpath)->next = NULL;
    }
    if (pathlength > (m*n)) {
    //if (pathlength > 50) {
      fprintf(stderr, "ERROR!! Permitted path length exceeded.\n");
      free(visited);
      return false;
    }
  }
  free(visited);
  if (pathlen != NULL) *pathlen = pathlength;
  if (pathcost == M[m*S_y + S_x]) return true;
  fprintf(stderr, "\nError calculating least path cost. Path = %i Matrix = %i\n", pathcost, M[m*S_y + S_x]);
  return false;
}

void getformat(char *format, int32_t max) {
  int32_t maxmax = 10;
  int32_t digits = 1;
  if (max < 10) {
    sprintf(format, "%s", "%i ");
    return;
  }
  while (max > maxmax) {
    digits++;
    maxmax *= 10;
    if (digits == 9) break;
  }
  sprintf(format, "%%0%ii ", digits);
  return;
}

void printa(int16_t *a, int16_t m, int16_t n) {  
  int32_t i, j;
  int16_t temp, max=0;
  char format[6];
  for (i=0; i<n; i++) {
    for (j=0; j<m; j++) {
      temp = a[i*m + j];
      max = (max > temp ? max : temp);
    }
  }
  getformat(format, (int32_t)max);
  for (i=0; i<n; i++) {
    for (j=0; j<m; j++) {
      printf(format, a[i*m + j]);
    }
    printf("\n");
  }
  return;
}

void printM(int32_t *M, int16_t m, int16_t n) {  
  int32_t i, j;
  int32_t temp, max=0;
  char format[6];
  for (i=0; i<n; i++) {
    for (j=0; j<m; j++) {
      temp = M[i*m + j];
      max = (max > temp ? max : temp);
    }
  }
  getformat(format, (int32_t)max);
  for (i=0; i<n; i++) {
    for (j=0; j<m; j++) {
      printf(format, M[i*m + j]);
    }
    printf("\n");
  }
  return;
}

void setM(int32_t *M, int32_t value, int16_t m, int16_t n) {  
  int32_t i, j;
  for (i=0; i<n; i++) {
    for (j=0; j<m; j++) {
      M[i*m + j] = value;
    }
  }
  return;
}


static inline int32_t kub(int32_t *M, int16_t *a, int16_t x, int16_t y, int16_t m, int16_t n, int32_t maxub) {  
  // Returns a known upper bound from the adjacent nodes for the minimum cost at x, y
  int32_t up, down, left, right;
  int32_t temp1, temp2, axy = a[y*m+x];
  if (x > 0) {
    left = M[y*m + x - 1];
  } else {
    left = maxub;
  }
  if ((x+1) < m) {
    right = M[y*m + x + 1];
  } else {
    right = maxub;
  }
  if ((y+1) < n) {
    down = M[(y+1)*m + x];
  } else {
    down = maxub;
  }
  if (y > 0) {
    up = M[(y-1)*m + x];
  } else {
    up = maxub;
  }
  temp1 = MIN(left, right);
  temp2 = MIN(up, down);
  return axy + MIN(temp1, temp2);
}

int64_t asum(int16_t *a, int16_t m, int16_t n) {  
  int16_t i, j;
  int64_t sum=0;
  for (i=0; i<n; i++) {
    for (j=0; j<m; j++) {
      sum += a[i*m+j];
    }
  }
  return sum;
}

void randomizea(int16_t *a, int16_t m, int16_t n) {  
  int16_t i, j;
  for (i=0; i<n; i++) {
    for (j=0; j<m; j++) {
      a[i*m+j] = (rand() % 10);
    }
  }
  return;
}

int64_t calcM(int32_t *M, int16_t *a, int16_t m, int16_t n, int16_t E_x, int16_t E_y, int32_t maxub) {
  M[E_y*m + E_x] = a[E_y*m + E_x];
  _Bool ubsupdated = true;
  int32_t i,j,temp;
  int64_t iterations = 0;
  while (ubsupdated) {
    iterations++;
    ubsupdated = false;
    for (i=E_x; i>=0; i--) { // top left quadrant
      for (j=E_y; j>=0; j--) {
        temp = kub(M,a,i,j,m,n,maxub);
        if (M[j*m + i] > temp) {
          M[j*m + i] = temp;
          ubsupdated = true;
        }
      }
    }
    for (i=E_x; i<m; i++) { // top right quadrant
      for (j=E_y; j>=0; j--) {
        temp = kub(M,a,i,j,m,n,maxub);
        if (M[j*m + i] > temp) {
          M[j*m + i] = temp;
          ubsupdated = true;
        }
      }
    }
    for (i=E_x; i>=0; i--) { // bottom left quadrant
      for (j=E_y; j<n; j++) {
        temp = kub(M,a,i,j,m,n,maxub);
        if (M[j*m + i] > temp) {
          M[j*m + i] = temp;
          ubsupdated = true;
        }
      }
    }
    for (i=E_x; i<m; i++) { // bottom right quadrant
      for (j=E_y; j<n; j++) {
        temp = kub(M,a,i,j,m,n,maxub);
        if (M[j*m + i] > temp) {
          M[j*m + i] = temp;
          ubsupdated = true;
        }
      }
    }
  }
  return iterations;
}


int main(int argc, char*argv[]) {
  if (argc < 5) {
    printf("This program generates an m column by n row array of random non-negative numbers representing costs. ");
    printf("It then calculates an m column by n row array of minimum costs of a journey to a destination element (Ex,Ey). ");
    printf("The path taken can include moves up, down, left, or right only. ");
    printf("No diagonal moves or moves off the edge of the array are allowed. ");
    printf("The total cost of a journey is the sum of all the element costs along its path.\n");
    printf("Optionally, use Sx, Sy for an example least cost path. (Outputs leastcostpath.htm)\n");
    printf("Author: Simon Goater Mar 2024.\n");
    printf("Usage:- %s m n Ex Ey [Sx Sy]\n", argv[0]);
    printf("1 <= m,n <= 32767\n");
    printf("0 <= Ex,Sx < m\n");
    printf("0 <= Ey,Sy < n\n");
    printf("e.g. %s 20 20 5 4 18 12\n", argv[0]);
    exit(0);
  }
  int32_t m = atoi(argv[1]);
  assert(m > 0);
  assert(m < 32768);
  int32_t n = atoi(argv[2]);
  assert(n > 0);
  assert(n < 32768);
  int32_t E_x = atoi(argv[3]);
  assert(E_x >= 0);
  assert(E_x < m);
  int32_t E_y = atoi(argv[4]);
  assert(E_y >= 0);
  assert(E_y < n);
  uint64_t thistime = time(0);
  srand(thistime);
  int16_t *a = malloc(n*m*sizeof(int16_t));
  assert(a != NULL);
  randomizea(a,m,n);
  int64_t maxub = 1+asum(a, m, n);
  assert(maxub <= 0x7fffffffULL);
  printa(a, m, n);
  int32_t pathlength;
  int32_t *M = malloc(n*m*sizeof(int32_t)); 
  assert(M != NULL);
  setM(M, maxub, m, n);
  int64_t iterations = calcM(M, a, m, n, E_x, E_y, maxub);
  //printM(M, m, n);
  printf("%li iterations required.\n", iterations);  
  if (argc >= 7) {
    int32_t S_x = atoi(argv[5]);
    assert(S_x >= 0);
    assert(S_x < m);
    int32_t S_y = atoi(argv[6]);
    assert(S_y >= 0);
    assert(S_y < n);
    leastcostpathnode_t *leastcostpathroot = NULL;
    leastcostpathnode_t *leastcostpathhead = NULL;
    if (findleastcostpath(&leastcostpathroot, &leastcostpathhead, E_x, E_y, S_x, S_y, &pathlength, M, a, m, n, maxub)) {
      printf("Least Cost Path example has %i nodes and cost %i.\n", pathlength, M[m*S_y + S_x]);
      printleastcostpath(*leastcostpathroot);
      printleastcostpathhtml(*leastcostpathroot, a, m, n, "leastcostpath.htm");
      freelist((void**)&leastcostpathroot, (void**)&leastcostpathhead);
    } else {
      fprintf(stderr, "ERROR!! Call to findleastcostpath() failed.\n");
    }
  }
  free(M);
  free(a);
}

/*
SSE performance of below for kub approx 2x slower
  if (ym > m) {     
    ix = ym + x - 1;
    __m128i cells = _mm_setr_epi32(M[ix], M[ix + 2], M[ix + 1 - m], M[ix + m + 1]); //left, right, up, down
    cells = _mm_sub_epi32(cells, _mm_set1_epi32(maxub));
    __m128i conditions1 = _mm_setr_epi32(x,m,y,n); 
    __m128i conditions2 = _mm_setr_epi32(0,x+1,0,y+1); 
    conditions1 = _mm_cmpgt_epi32(conditions1, conditions2);
    cells = _mm_add_epi32(_mm_set1_epi32(maxub), _mm_and_si128(conditions1, cells));
    return axy + X_mm_hmin_epi32(cells);
*/
