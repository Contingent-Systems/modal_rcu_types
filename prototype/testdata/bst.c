// A binary search tree node, with RCU-typed children.
#define __rcu __attribute__((annotate("__rcu")))

struct node {
  int key;
  struct node * __rcu left;
  struct node * __rcu right;
};

void synchronize_rcu(void);
void kfree(void *);

// Correct: unlink, wait out a grace period, then reclaim.
void delete_ok(struct node *parent, struct node *current)
{
  struct node *l = current->left;
  parent->left = l;
  synchronize_rcu();
  kfree(current);
}

// Wrong: reclaimed without waiting.  A reader that entered before the
// unlink may still hold a reference.
void delete_too_soon(struct node *parent, struct node *current)
{
  struct node *l = current->left;
  parent->left = l;
  kfree(current);
}
