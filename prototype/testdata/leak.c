// A node unlinked on one path and not reclaimed.
#define __rcu __attribute__((annotate("__rcu")))
struct node { int key; struct node * __rcu left; struct node * __rcu right; };
void synchronize_rcu(void);
void kfree(void *);

// Wrong: on the branch that unlinks, cur is never freed, so it leaks.
void maybe_unlink(struct node *parent, int flag)
{
  struct node *cur = parent->left;
  struct node *l   = cur->left;
  if (cur->right == 0) {
    if (parent->left == cur) {
      parent->left = l;
    }
  }
}
