// A binary search tree with RCU-typed children, and one correct and one
// incorrect reclamation.
//
//   ../rcu-check bst.c --assume-entry -- -std=c11

#define __rcu __attribute__((annotate("__rcu")))

struct node {
  int key;
  struct node * __rcu left;
  struct node * __rcu right;
};

void  synchronize_rcu(void);
void  kfree(void *);
void *kmalloc(unsigned long);

// Correct.  The replacement is built as a copy of the node it replaces, spliced
// in, and the old node reclaimed only after a grace period.
void replace_ok(struct node *parent)
{
  struct node *cur = parent->left;
  struct node *l   = cur->left;
  struct node *r   = cur->right;

  struct node *n = kmalloc(sizeof(struct node));
  n->left  = l;
  n->right = r;

  parent->left = n;
  synchronize_rcu();
  kfree(cur);
}

// Wrong.  The same sequence without the grace period: a reader that entered
// before the splice may still hold a reference to cur when it is freed.
void replace_too_soon(struct node *parent)
{
  struct node *cur = parent->left;
  struct node *l   = cur->left;
  struct node *r   = cur->right;

  struct node *n = kmalloc(sizeof(struct node));
  n->left  = l;
  n->right = r;

  parent->left = n;
  kfree(cur);
}
