// Interprocedural: a helper that reclaims, and callers that use it.
//
//   ../rcu-check calls.c -- -std=c11

#define __rcu __attribute__((annotate("__rcu")))
struct node { int key; struct node * __rcu left; struct node * __rcu right; };
void synchronize_rcu(void);
void kfree(void *);

// Takes a node already unlinked, waits out a grace period, reclaims it.
// Its summary is inferred: the parameter must be unlinked on entry.
void reclaim(struct node *victim)
{
  synchronize_rcu();
  kfree(victim);
}

// Correct: unlink, then hand the node to reclaim.
void delete_ok(struct node *parent)
{
  struct node *cur = parent->left;
  struct node *l   = cur->left;
  if (cur->right == 0) {
    if (parent->left == cur) {
      parent->left = l;
      reclaim(cur);
    }
  }
}

// Wrong: hands reclaim a node that is still in the structure.
void delete_bad(struct node *parent)
{
  struct node *cur = parent->left;
  reclaim(cur);
}
