// The binary search tree delete of Appendix D, as C.
//
//   ../rcu-check bst_delete.c -- -std=c11
//
// The paper's own example, transcribed rather than invented.  Two versions of
// the same traversal, and the difference between them is the point.

#define __rcu __attribute__((annotate("__rcu")))

struct node {
  int key;
  struct node * __rcu Left;
  struct node * __rcu Right;
};

void  synchronize_rcu(void);
void  kfree(void *);
void *kmalloc(unsigned long);

// Self-contained: the cursor is read out of the root, so the checker knows
// current is parent's child, which is what the loop needs to stay invariant.
void tree_delete(struct node *root, int toDel)
{
  struct node *parent  = root;
  struct node *current = parent->Left;

  while (current->key != toDel) {
    struct node *nxt = current->Left;
    parent = current;
    current = nxt;
  }

  struct node *currentL = current->Left;

  if (current->Right == 0) {
    if (parent->Left == current) {
      parent->Left = currentL;
      synchronize_rcu();
      kfree(current);
    }
  }
}

// The same body, but taking the two cursors as parameters.  Nothing says they
// are related, so the loop has no invariant: on entry the two paths are
// independent, and after one iteration the first has become the second.  A
// path-level summary would carry the relationship; a kind-level one cannot.
void tree_delete_params(struct node *parent, struct node *current, int toDel)
{
  while (current->key != toDel) {
    struct node *nxt = current->Left;
    parent = current;
    current = nxt;
  }
  struct node *currentL = current->Left;
  if (current->Right == 0) {
    if (parent->Left == current) {
      parent->Left = currentL;
      synchronize_rcu();
      kfree(current);
    }
  }
}
