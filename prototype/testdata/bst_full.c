// The complete binary search tree delete of Appendix D.
//
//   ../rcu-check bst_full.c -- -std=c11
//
// The traversal and two of the three rethreading cases: the one where the node
// has no right child, and the two-child case that allocates a copy of the
// successor and replaces the node with it.  The second is the hardest thing the
// type system claims to check, and the appendix annotates every line of it.
//
// It type checks, and not vacuously: removing the grace period, or leaving one
// field out of the copy, are both rejected -- the second by the mirroring
// premise, with the message that the copy would not mirror what it replaces.

#define __rcu __attribute__((annotate("__rcu")))

struct node {
  int key;
  struct node * __rcu Left;
  struct node * __rcu Right;
};

void  synchronize_rcu(void);
void  kfree(void *);
void *kmalloc(unsigned long);

void tree_delete(struct node *root, int toDel)
{
  struct node *parent  = root;
  struct node *current = parent->Left;

  while (current->key != toDel) {
    struct node *nxt = current->Left;
    parent  = current;
    current = nxt;
  }

  struct node *currentL = current->Left;
  struct node *lmParent = current->Right;

  // CASE 1: no right child -- the left child takes current's place.
  if (current->Right == 0) {
    if (parent->Left == current) {
      parent->Left = currentL;
      synchronize_rcu();
      kfree(current);
    }
  }

  // CASE 3: the right child's left-most descendant replaces current.  A copy
  // of it is built first, spliced in, and only then is the original unlinked.
  else {
    struct node *currentF = kmalloc(sizeof(struct node));
    currentF->Right = lmParent;
    currentF->Left  = currentL;

    if (parent->Left == current) {
      parent->Left = currentF;
      synchronize_rcu();
      kfree(current);
    }
  }
}

// The same two-child case with the copy left incomplete.  Rejected: a
// replacement that does not mirror the node it replaces moves a subtree
// instead of preserving it, which is what the side condition on T-Replace is
// there to prevent.
void tree_delete_bad_copy(struct node *root, int toDel)
{
  struct node *parent  = root;
  struct node *current = parent->Left;

  while (current->key != toDel) {
    struct node *nxt = current->Left;
    parent  = current;
    current = nxt;
  }

  struct node *currentL = current->Left;
  struct node *lmParent = current->Right;

  struct node *currentF = kmalloc(sizeof(struct node));
  currentF->Right = lmParent;

  if (parent->Left == current) {
    parent->Left = currentF;
    synchronize_rcu();
    kfree(current);
  }
}
