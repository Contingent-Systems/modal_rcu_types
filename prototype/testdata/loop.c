// Loops and branches, to exercise the CFG and the widening at back edges.
//
//   ../rcu-check loop.c --assume-entry -- -std=c11

#define __rcu __attribute__((annotate("__rcu")))

struct node {
  int key;
  struct node * __rcu next;
};

void  synchronize_rcu(void);
void  kfree(void *);
void *kmalloc(unsigned long);

// A plain traversal.  The cursor's path grows by one step per iteration, so
// the loop only closes once the back edge is widened to an abstract number of
// steps.  Accepted.
struct node *find(struct node *head, int target)
{
  struct node *cur = head->next;
  while (cur->key != target) {
    struct node *nxt = cur->next;
    cur = nxt;
  }
  return cur;
}

// A branch, joined afterwards.  Accepted.
struct node *pick(struct node *head, int which)
{
  struct node *a = head->next;
  if (which) {
    struct node *b = a->next;
    return b;
  }
  return a;
}

// Wrong, and the reason is worth reading.  After the loop the cursor is an
// abstract number of steps from the head, so it is not head's child any more,
// and replacing head->next with a copy of it would splice the copy in at the
// wrong depth.  Rejected.
void walk_then_replace(struct node *head, int target)
{
  struct node *cur = head->next;
  while (cur->key != target) {
    struct node *nxt = cur->next;
    cur = nxt;
  }

  struct node *n = kmalloc(sizeof(struct node));
  struct node *t = cur->next;
  n->next = t;

  head->next = n;
  synchronize_rcu();
  kfree(cur);
}
