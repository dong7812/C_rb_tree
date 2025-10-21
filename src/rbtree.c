#include "rbtree.h"

#include <stdlib.h>

// --- forward static prototypes (add this block) ---
// Note: node_t is assumed to be defined in rbtree.h
static void     free_subnodes(rbtree *t, node_t *n);
static node_t  *find_min(const rbtree *t, node_t *n);
static node_t  *find_max(const rbtree *t, node_t *n);
static void     insert_fixedup(rbtree *t, node_t *p);
static void     array_subnodes(const rbtree *t, node_t *n, key_t *arr, size_t ncap, size_t *idx);
// u 자리에 v 서브트리를 이식(transplant): 부모 포인터까지 교체
static void     transplant(rbtree *t, node_t *u, node_t *v);
// 삭제 균형보정: x가 sentinel(NULL 대용)일 수 있으므로 x의 부모를 따로 전달
static void     erase_fixedup(rbtree *t, node_t *x, node_t *x_parent);
// ---------------------------------------------------

// Helper to check node color, treats NULL or t->nil as BLACK
static inline color_t node_color(const rbtree *t, node_t *n) {
  return (n == NULL || n == t->nil) ? RBTREE_BLACK : n->color;
}

rbtree *new_rbtree(void)
{
  rbtree *p = (rbtree *)calloc(1, sizeof(*p));

  if (p == NULL){
    return NULL;
  }

  node_t *sentinel = (node_t *)calloc(1, sizeof(*sentinel));

  if (sentinel == NULL){
    free(p);
    return NULL;
  }

  // Set up the sentinel node
  sentinel->color = RBTREE_BLACK;
  sentinel->left = sentinel->right = sentinel->parent = sentinel;

  p->nil = sentinel;
  p->root = NULL; // Initial root is NULL (테스트에서 루트의 parent==NULL 기대)

  return p;
}

static void free_subnodes(rbtree *t, node_t *n)
{
  // n == t->nil도 처리해야 하므로, t->nil인 경우에도 종료
  if (n == NULL || n == t->nil)
    return;

  free_subnodes(t, n->left);
  free_subnodes(t, n->right);
  free(n);
}

void delete_rbtree(rbtree *t)
{
  // 후위 순회로 진행되어야 한다. (재귀로 하위부터 free)
  if (t == NULL){
    return;
  }

  // t->root가 NULL이 아니면 free_subnodes 호출
  if (t->root != NULL) {
    free_subnodes(t, t->root);
  }

  free(t->nil);
  free(t);
}

// x를 기준으로 왼쪽 회전: x의 오른쪽 자식 y가 위로 올라옴
void left_rotation(rbtree *t, node_t *x)
{
  // 올라올 노드
  node_t *y = x->right;
  // y의 왼쪽 자식 (회전 후 x의 오른쪽 자식이 됨)
  node_t *temp = y->left;

  // 1) y의 왼쪽 서브트리를 x의 오른쪽으로 붙인다
  // temp는 항상 t->nil이거나 실제 노드여야 함 (NULL로 강제 변환 금지!)
  x->right = temp;
  if (temp != t->nil && temp != NULL){
    temp->parent = x;
  }

  // 2) y를 x의 부모 자리에 올린다
  // 루트 노드 체크는 t->nil을 사용하도록 일관성 확보
  y->parent = x->parent;
  if (x->parent == NULL || x->parent == t->nil){
    // x가 루트였다면 이제 y가 루트, 루트의 parent는 NULL로 유지 (테스트 요구사항)
    t->root = y;
    y->parent = NULL;
  }
  else if (x == x->parent->left){
    x->parent->left = y;
  }
  else{
    x->parent->right = y;
  }

  // 3) x를 y의 왼쪽 자식으로 내린다
  y->left = x;
  x->parent = y;
}

// x를 기준으로 오른쪽 회전: x의 왼쪽 자식 y가 위로 올라옴
void right_rotation(rbtree *t, node_t *x)
{
  // 올라올 노드
  node_t *y = x->left;
  // y의 오른쪽 자식 (회전 후 x의 왼쪽 자식이 됨)
  node_t *temp = y->right;

  // y의 오른쪽 서브트리를 x의 왼쪽으로 붙인다
  // temp는 항상 t->nil이거나 실제 노드여야 함 (NULL로 강제 변환 금지!)
  x->left = temp;
  if (temp != t->nil && temp != NULL){
    temp->parent = x;
  }

  // y를 x의 부모 자리에 올린다
  // 루트 노드 체크는 t->nil을 사용하도록 일관성 확보
  y->parent = x->parent;
  if (x->parent == NULL || x->parent == t->nil){
    // x가 루트였다면 이제 y가 루트, 루트의 parent는 NULL
    t->root = y;
    y->parent = NULL;
  }
  else if (x == x->parent->right){
    x->parent->right = y;
  }
  else{
    x->parent->left = y;
  }

  // x를 y의 오른쪽 자식으로 내린다
  y->right = x;
  x->parent = y;
}

node_t *rbtree_min(const rbtree *t)
{
  if (!t || t->root == NULL)
    return NULL;
  return find_min(t, t->root);
}

static node_t *find_min(const rbtree *t, node_t *n)
{
  // n의 왼쪽 자식이 t->nil이거나 NULL일 때 멈춤
  if (n->left == NULL || n->left == t->nil) return n;
  return find_min(t, n->left);
}

node_t *rbtree_max(const rbtree *t)
{
  if (!t || t->root == NULL)
    return NULL;

  return find_max(t, t->root);
}

static node_t *find_max(const rbtree *t, node_t *n)
{
  // n의 오른쪽 자식이 t->nil이거나 NULL일 때 멈춤
  if (n->right == NULL || n->right == t->nil) return n;
  return find_max(t, n->right);
}

node_t *rbtree_insert(rbtree *t, const key_t key)
{
  // key와 비교가 될 node
  node_t *x = t->root ? t->root : t->nil;
  // key node의 부모가 될 y
  node_t *y = t->nil;
  // key로 찾은 node
  node_t *z = (node_t *)calloc(1, sizeof(*z));

  if (z == NULL) return NULL; // 메모리 할당 실패 처리

  // 자식으로 들어가게 될 z에 대한 기본 선언
  z->key   = key;
  z->color = RBTREE_RED;

  // FIX for test-rbtree.c assertion:
  // 새 노드의 자식을 NULL로 설정하여 단일 노드 테스트 케이스를 만족시킴
  z->left = NULL;
  z->right = NULL;
  z->parent = t->nil;

  // rbtree에서 어디에 들어갈지 순회하면서 위치 파악
  while (x != t->nil && x != NULL)
  {
    y = x;
    if (key < x->key){
      x = x->left;
      // x가 NULL이면 다음 루프에서 y가 부모가 되고 루프 종료
    }
    else{
      x = x->right;
    }
  }

  // 부모 확정
  z->parent = y;

  if (y == t->nil){
    t->root = z;
  }
  else if (key < y->key){
    y->left = z;
  }
  else{
    y->right = z;
  }

  // 보정
  insert_fixedup(t, z);

  // 루트가 NULL이 아닌 경우에만 부모를 NULL로 설정(테스트 요구)
  if (t->root != NULL) {
    t->root->parent = NULL;
  }

  return z;
}

void insert_fixedup(rbtree *t, node_t *p)
{
  // p의 부모가 RED인 동안 보정
  while (p->parent != NULL && p->parent != t->nil && node_color(t, p->parent) == RBTREE_RED)
  {
    // p의 부모의 부모(gp). NULL이면 t->nil로 취급
    node_t *gp = p->parent->parent;
    if (gp == NULL) gp = t->nil;

    if (p->parent == gp->left)
    {
      // Uncle Node (y)
      node_t *y = gp->right;
      if (y == NULL) y = t->nil;

      if (node_color(t, y) == RBTREE_RED)
      {
        // Case 1: Uncle is RED
        p->parent->color = RBTREE_BLACK;
        y->color = RBTREE_BLACK;
        gp->color = RBTREE_RED;
        p = gp;
      }
      else
      {
        // Case 2: Uncle is BLACK, p가 오른쪽 자식
        if (p == p->parent->right)
        {
          p = p->parent;
          left_rotation(t, p);
        }
        // Case 3: Uncle is BLACK, p가 왼쪽 자식 (또는 Case2 이후)
        p->parent->color = RBTREE_BLACK;
        gp->color = RBTREE_RED;
        right_rotation(t, gp);
      }
    }
    else // p->parent == gp->right
    {
      // Uncle Node (y)
      node_t *y = gp->left;
      if (y == NULL) y = t->nil;

      if (node_color(t, y) == RBTREE_RED)
      {
        // Case 1: Uncle is RED
        p->parent->color = RBTREE_BLACK;
        y->color = RBTREE_BLACK;
        gp->color = RBTREE_RED;
        p = gp;
      }
      else
      {
        // Case 2: Uncle is BLACK, p가 왼쪽 자식
        if (p == p->parent->left)
        {
          p = p->parent;
          right_rotation(t, p);
        }
        // Case 3: Uncle is BLACK, p가 오른쪽 자식 (또는 Case2 이후)
        p->parent->color = RBTREE_BLACK;
        gp->color = RBTREE_RED;
        left_rotation(t, gp);
      }
    }
  }
  // 루트는 항상 BLACK (NULL이 아닌 경우에만)
  if (t->root != NULL) {
    t->root->color = RBTREE_BLACK;
  }
}

node_t *rbtree_find(const rbtree *t, const key_t key)
{
  node_t *x = t->root;

  // 자식 포인터를 NULL로 쓰는 테스트 규약에 맞춤
  while (x != NULL && x != t->nil) {
    if (key < x->key) {
      x = x->left;
    } else if (key > x->key) {
      x = x->right;
    } else {
      return x;  // 찾음
    }
  }
  return NULL;
}

// u 자리에 v 서브트리를 이식(transplant): 부모 포인터까지 교체
static void transplant(rbtree *t, node_t *u, node_t *v)
{
  // v가 NULL이면, u의 자리에 t->nil을 이식할 준비를 한다.
  node_t *newv = (v == NULL) ? t->nil : v;

  if (u->parent == NULL || u->parent == t->nil) {
    // u가 루트인 경우: 루트는 NULL 또는 실제 노드여야 함
    t->root = (newv == t->nil) ? NULL : newv;
    if (t->root != NULL) {
      t->root->parent = NULL; // 루트의 부모는 NULL
    }
  } else if (u == u->parent->left) {
    u->parent->left = newv;
  } else {
    u->parent->right = newv;
  }

  // newv가 t->nil이 아닌 실제 노드인 경우에만 부모를 업데이트
  if (newv != t->nil) {
    newv->parent = u->parent;
  }
}

// 삭제 균형보정: x가 sentinel(NULL 대용)일 수 있으므로 x의 부모를 따로 전달
static void erase_fixedup(rbtree *t, node_t *x, node_t *x_parent)
{
  // x가 루트가 아니고 색이 BLACK인 동안
  while (x != t->root && node_color(t, x) == RBTREE_BLACK) {
    // x가 sentinel일 때를 위해 부모를 파라미터로 받음
    node_t *parent = (x == t->nil) ? x_parent : x->parent;

    if (parent == NULL) break; // 안전장치

    if (x == parent->left) {
      node_t *w = parent->right;
      if (w == NULL) w = t->nil;

      // Case 1: 형제가 RED
      if (node_color(t, w) == RBTREE_RED) {
        w->color = RBTREE_BLACK;
        parent->color = RBTREE_RED;
        left_rotation(t, parent);
        w = parent->right;
        if (w == NULL) w = t->nil;
      }

      // Case 2: 형제의 두 자식이 모두 BLACK
      if (node_color(t, w->left) == RBTREE_BLACK && node_color(t, w->right) == RBTREE_BLACK) {
        if (w != t->nil) {
          w->color = RBTREE_RED;
        }
        x = parent;
        x_parent = (x == t->nil) ? NULL : x->parent;
      } else {
        // Case 3: 형제의 오른쪽이 BLACK (왼쪽은 RED)
        if (node_color(t, w->right) == RBTREE_BLACK) {
          if (w->left != t->nil && w->left != NULL){
            w->left->color = RBTREE_BLACK;
          }
          w->color = RBTREE_RED;
          right_rotation(t, w);
          w = parent->right;
          if (w == NULL) w = t->nil;
        }
        // Case 4: 형제의 오른쪽이 RED
        w->color = parent->color;
        parent->color = RBTREE_BLACK;
        if (w->right != t->nil && w->right != NULL){
          w->right->color = RBTREE_BLACK;
        }
        left_rotation(t, parent);
        x = t->root; // 루프 종료
      }
    } else {
      // 위의 대칭 (x가 오른쪽 자식일 때)
      node_t *w = parent->left;
      if (w == NULL) w = t->nil;

      // Case 1
      if (node_color(t, w) == RBTREE_RED) {
        w->color = RBTREE_BLACK;
        parent->color = RBTREE_RED;
        right_rotation(t, parent);
        w = parent->left;
        if (w == NULL) w = t->nil;
      }
      // Case 2
      if (node_color(t, w->right) == RBTREE_BLACK && node_color(t, w->left) == RBTREE_BLACK) {
        if (w != t->nil) {
          w->color = RBTREE_RED;
        }
        x = parent;
        x_parent = (x == t->nil) ? NULL : x->parent;
      } else {
        // Case 3: 형제의 왼쪽이 BLACK (오른쪽은 RED)
        if (node_color(t, w->left) == RBTREE_BLACK) {
          if (w->right != t->nil && w->right != NULL){
            w->right->color = RBTREE_BLACK;
          }
          w->color = RBTREE_RED;
          left_rotation(t, w);
          w = parent->left;
          if (w == NULL) w = t->nil;
        }
        // Case 4
        w->color = parent->color;
        parent->color = RBTREE_BLACK;
        if (w->left != t->nil && w->left != NULL){
          w->left->color = RBTREE_BLACK;
        }
        right_rotation(t, parent);
        x = t->root; // 루프 종료
      }
    }
  }
  // 루트는 항상 BLACK (NULL이나 sentinel이 아닌 경우)
  if (x != NULL && x != t->nil) {
    x->color = RBTREE_BLACK;
  }
}

int rbtree_erase(rbtree *t, node_t *p)
{
  // p 노드를 트리에서 제거한다
  if (t == NULL || p == NULL || p == t->nil) return 0;

  // 실제로 삭제될(or 이동될) 노드
  node_t *y = p;
  // y의 자리에 오를 서브트리의 루트
  node_t *x;
  // x가 sentinel일 수 있으므로 x의 부모를 따로 추적
  node_t *x_parent = NULL;
  // 삭제 전 색 저장
  color_t y_original_color = y->color;

  if (p->left == NULL || p->left == t->nil) {
    // 왼쪽 자식 없음: 오른쪽 자식을 올린다
    x = p->right;
    if (x == NULL) x = t->nil;           // NULL을 sentinel로 치환
    x_parent = p->parent;                 // p가 제거되면 x의 새로운 부모 기준
    transplant(t, p, p->right);

  } else if (p->right == NULL || p->right == t->nil) {
    // 오른쪽 자식 없음: 왼쪽 자식을 올린다
    x = p->left;
    if (x == NULL) x = t->nil;           // NULL을 sentinel로 치환
    x_parent = p->parent;
    transplant(t, p, p->left);

  } else {
    // 양쪽 자식 모두 있음: 후속자(오른쪽 서브트리의 최소)를 올린다
    y = find_min(t, p->right);
    y_original_color = y->color;
    x = y->right;
    if (x == NULL) x = t->nil;           // NULL을 sentinel로 치환

    if (y->parent == p) {
      // 후속자가 바로 p의 오른쪽인 경우
      x_parent = y;                      // x의 부모는 y
    } else {
      // y를 그 자리에서 제거하고 y의 오른쪽 자식을 그 자리에 올림
      x_parent = y->parent;              // x가 sentinel일 수 있으니 미리 저장
      transplant(t, y, y->right);
      // 이제 y의 오른쪽을 p의 오른쪽으로 붙임
      y->right = p->right;
      y->right->parent = y;
    }

    // p의 자리에 y를 올린다
    transplant(t, p, y);
    y->left = p->left;
    if (y->left != NULL && y->left != t->nil){
      y->left->parent = y;
    }
    y->color = p->color;
  }

  // 실제 삭제 대상이 BLACK이면 균형 보정 필요
  if (y_original_color == RBTREE_BLACK) {
    erase_fixedup(t, x, x_parent);
  }

  // 삭제된 노드 p의 자식/부모 포인터를 초기화하여 깨끗하게 만든 후 해제
  p->left = p->right = p->parent = NULL;
  free(p);
  return 0;
}

int rbtree_to_array(const rbtree *t, key_t *arr, const size_t n)
{
  if (!t || !arr || n == 0 || t->root == NULL) {
    return 0;
  }

  size_t i = 0;
  array_subnodes(t, t->root, arr, n, &i);
  return (int)i;
}

static void array_subnodes(const rbtree *t, node_t *n, key_t *arr, size_t ncap, size_t *idx)
{
  if (n == NULL || n == t->nil || *idx == ncap) return;

  array_subnodes(t, n->left, arr, ncap, idx);

  // 이 array에 삽입할거 (중위 순회로 오름차순 저장)
  if (*idx < ncap) {
    arr[(*idx)++] = n->key;   // append 느낌으로
  }

  array_subnodes(t, n->right, arr, ncap, idx);
}