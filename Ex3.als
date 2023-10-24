//Ex3
module Ex3

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
  all dl: HeadNode | dl.lst != none && dl.frst != none implies dl.lst in dl.frst.^nnext + dl.frst
}

fact HasLstandFrst{
    // Indicates that if there is a frst, there is also an lst, and vice-versa 
    all dl : HeadNode | dl.lst != none implies dl.frst != none 
    all dl : HeadNode | dl.frst != none implies dl.lst != none
}

fact AllNodesBelongToDoublyLinkedList {
  //All nodes belong to one doubly-linked list
  all n: Node | (n.nnext != none || n.nprev != none) implies n in (HeadNode.frst.^nnext + HeadNode.frst)
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

//Ex 3.3

-- Insert operation: Insert a node 'n' at the end of the doubly-linked list headed by 'hn'
pred insert[n: Node, hn: HeadNode] {
  -- Pre-conditions
  -- Pre1 - 'n' is not already in the list
  no (hn.frst.^nnext + hn.frst & n)
  -- Pre2 - 'n' is not attach to any list 
  no hnode: HeadNode |  n in (hnode.frst.^nnext + hnode.frst)
  -- Pre3 - verify if the n.nnext and n.nprev is none
  n.nnext = none and n.nprev = none
  
  -- Post-conditions
  -- Post1 - 'n' becomes the new 'lst' of 'hn'
  hn.lst' = n
  -- Post2 - The old 'lst' becomes the 'nprev' of 'n'
  n.nprev' = hn.lst
  -- Post 3 - The 'n' becomes the 'nnext' of the old 'lst' 
  hn.lst.nnext' = n
  -- Post 4 - The new lst has the nnext set to none 
  n.nnext' = none 
  
  -- Frame-conditions
  -- Frame 1 - 'nprev' and 'nnext' relationships of other nodes do not change
  all node: Node - (n + hn.lst) |  node.nprev' = node.nprev and node.nnext' = node.nnext
  -- Frame 2 - 'frst' of 'hn' does not change
  hn.frst' = hn.frst
  -- Frame 3 - todos os prev ficam na mesma 
  all node:Node - (n) | node.nprev' = node.nprev
}

-- Remove operation: Remove a node 'n' from the doubly-linked list headed by 'hn'
pred remove[n: Node, hn: HeadNode] {
  -- Pre-conditions
  -- Pre 1 - 'n' belongs to the list
  n in hn.frst.^nnext + hn.frst

  removeMiddleList[n,hn] //Case 1
  removeFrst[n,hn] //Case 2
  removeLst[n,hn] //Case 3
  removeOnly[n,hn] //Case 4 
}

//Caso 1
pred removeMiddleList[n: Node, hn: HeadNode] {
  -- Pre-condition
  -- Caso 1 - Node está no meio da Lista
  n != hn.frst && n != hn.lst

  -- Post-conditions
  // Post 1 - O node anterior passa a ter como next o next de n 
  n.nprev.nnext' = n.nnext 
  // Post 2 - O node seguinte passa a ter como prev o prev de n
  n.nnext.nprev' = n.nprev  
  // Post 3 - Apagar o Node da lista  
  n.nnext' = none
  n.nprev' = none

  -- Frame-conditions
  -- Frame 1 
  all node: Node - (n + n.nprev + n.nnext) | (node.nprev' = node.nprev and node.nnext' = node.nnext)
  -- Frame 2
  all node: Node - (n + n.nprev ) | (node.nnext' = node.nnext)
  -- Frame 3
  all node: Node - (n + n.nnext ) |  (node.nprev' = node.nprev)
  -- Frame4
  hn.frst' = hn.frst
  -- Frame5
  hn.lst' = hn.lst

}

//Caso 2
pred removeFrst [n: Node, hn: HeadNode] {
  -- Pre-condition
  -- Caso 2 - Node está no início da Lista
  n = hn.frst && n != hn.lst

  -- Post-conditions
  // Post 1 - O novo frst é o nnext de n 
  hn.frst' = n.nnext 
  // Post 2 - O novo frst tem o nprev a none 
  n.nnext.nprev' = none 
  // Post 3 - Apagar o Node da lista  
  n.nnext' = none
  n.nprev' = none

  -- Frame-conditions
  -- Frame 1
  all n1:Node - (n) | n1.nnext' = n1.nnext 
  -- Frame 2
  all n1:Node - (n + n.nnext) | n1.nprev' = n1.nprev
  -- Frame 3
  hn.lst' = hn.lst
}

//Caso 3
pred removeLst [n: Node, hn: HeadNode] {
  -- Pre-condition
  -- Caso 3 - Node está no fim da Lista 
  n != hn.frst && n = hn.lst

  -- Post-conditions
  // Post 1 - O novo lst é o nprev de n 
  hn.lst' = n.nprev and
  // Post 2 - O novo lst tem o nnext a none 
  n.nprev.nnext' = none
  // Post 3 - Apagar o Node da lista  
  n.nnext' = none
  n.nprev' = none

  -- Frame-conditions
  -- Frame 1
  all n1:Node - (n) | n1.nprev' = n1.nprev 
  -- Frame 2
  all n1:Node - (n + n.nprev) |  n1.nnext' = n1.nnext 
  -- Frame 3
  hn.frst' = hn.frst
}

//Caso 4
pred removeOnly [n: Node, hn: HeadNode] {
  -- Pre-condition
  -- Caso 4 - Node é o único da Lista
  n = hn.frst && n = hn.lst

  -- Post-conditions
  // Post 1 - The node before 'n' becomes the new 'nnext' of the node after 'n'
  hn' = none
  // Post 2 - Apagar o Node da lista  
  n.nnext' = none
  n.nprev' = none

  -- Frame-conditions
  -- No Frame-conditions
}
