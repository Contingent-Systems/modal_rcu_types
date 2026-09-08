// Unlinking a node, which needs both refinements.
//
//   ../rcu-check unlink.c --assume-entry -- -std=c11

#define __rcu __attribute__((annotate("__rcu")))

struct node {
  int key;
  struct node * __rcu left;
  struct node * __rcu right;
};

void synchronize_rcu(void);
void kfree(void *);

// The one-child case of a tree delete.  Unlinking requires that every other
// field of the removed node is null, which only the test below establishes,
// and that the parent's field map records which child it is -- likewise.
void delete_one_child(struct node *parent)
{
  struct node *cur = parent->left;
  struct node *l   = cur->left;

  if (cur->right == 0) {
    if (parent->left == cur) {
      parent->left = l;
      synchronize_rcu();
      kfree(cur);
    }
  }
}
