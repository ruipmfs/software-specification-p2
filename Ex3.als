//Ex3

//Ex 3.1
sig Node {
  nprev: lone Node, // Each node has at most one previous node
  nnext: lone Node  // Each node has at most one next node
}

sig HeadNode {
  frst: one Node,      // The doubly-linked list has a frst node
  lst: one Node       // The doubly-linked list has a lst node
}

//Relation between Nodes 
fact NoCycles {
    // There are no cycles in the linked list
  no n: Node | n in n.^nprev && n in n.^nnext
}

fact NoSelfReference {
    // A node cannot refer to itself as the next or previous node 
  all n: Node | n.nprev != n && n.nnext != n
}

fact NNextNPrevRelationship {
    // Implies that if n2 is next to n1, then n1 is previous to n2  
  all n1, n2: Node | n1.nnext = n2 implies n2.nprev = n1
}

fact NPrevNNextRelationship {
    // Implies that if n2 is previous to n1, then n1 is next to n2 
  all n1, n2: Node | n1.nprev = n2 implies n2.nnext = n1
}


//Relation between HeadNode and Node
fact FrstHasNullNPrev {
    // The first node has nprev equal to 'none'
  all dl: HeadNode | dl.frst.nprev = none 
}

fact LstHasNullNNext {
    // The last node has nnext equal to 'none' 
  all dl: HeadNode | dl.lst.nnext = none 
}

fact DistinctFrstAndLs {
  // Ensures that 'lst' is reachable from 'frst' by following 'nnext' links
  all dl: HeadNode | dl.lst != none && dl.frst != none implies dl.lst in dl.frst.^nnext
}

fact HasLstandFrst{
    // Indicates that if there is a frst, there is also an lst, and vice-versa 
    all dl : HeadNode | dl.lst != none implies dl.frst != none 
    all dl : HeadNode | dl.frst != none implies dl.lst != none
}

fact AllNodesBelongToDoublyLinkedList {
  // All nodes belong to one doubly-linked list
  all n: Node | n in (HeadNode.frst.^nnext + HeadNode.frst)
}

fact DistinctFrstAndLst {
  // Ensures that diferent HeadNodes are pointing to different lists
  all dl1, dl2: HeadNode | dl1 != dl2 implies (dl1.lst != dl2.lst) && (dl1.frst != dl2.frst)
}


fact NoHeadNodeWithBothNone {
  // A HeadNode needs at least one Node to exist
  all dl: HeadNode | dl.lst != none && dl.frst != none
}

//Ex 3.2
run {} for exactly 2 HeadNode, exactly 5 Node
