open Ex3
open util/ordering[Id]

// Define OHeadNode as an extension of HeadNode
sig OHeadNode extends HeadNode {}

sig Id {}

// Define ONode signature
sig ONode extends Node {
  id: one Id
}

fact OrderedNodesInAscendingOrder {
  // Ensure nodes are arranged in ascending order based on their "id"
  always all o1, o2: ONode | o1 != o2 && o1.nnext = o2 implies o1.id.lt[o2.id]
}

fact IdneedsAONode {
  // All nodes belong to one doubly-linked list
  always all n: Id | n in (ONode.id)
}

fact DistinctFrstAndLst {
  // Ensures that different HeadNodes are pointing to different lists
  always all dl1, dl2: ONode | dl1 != dl2 implies dl1.id != dl2.id
}

fact OHeadNodepointsToONode {
  // If an ONode belongs to a
  always all node: ONode | node in HeadNode.frst.*nnext implies node in OHeadNode.frst.*nnext
}

// Ex 4.2
run { #OHeadNode >= 2 && #ONode >= 5 } for 6

// Ex 4.3
-- Insert operation: Insert a node 'n' in the ordered node
pred Oinsert[n: ONode, hn: OHeadNode] {
  OinsertNoElements[n, hn] // Case 1
  or
  OinsertLst[n, hn] // Case 2
  or
  OinsertFrst[n, hn] // Case 3
  or 
  OinsertMiddle[n,hn] // Case 4
}

pred OinsertNoElements[n: ONode, hn: OHeadNode]{
  -- Pre-conditions
  -- Pre 1 - 'n' is not attached to any list
  n ! in HeadNode.frst.*nnext
  -- Pre 2 - verify if the n.nnext and n.nprev are none
  n.nnext = none && n.nprev = none
  -- Pre 3 hn has no elements
  hn.frst = none && hn.lst = none

  -- Post-conditions
  -- Post 3 - The 'n' becomes the 'nnext' of the old 'lst'
  hn.frst' = n
  -- Post 1 - 'n' becomes the new 'lst' of 'hn'
  hn.lst' = n

  -- Frame-conditions
  all headNode : (HeadNode - hn) | headNode.frst'.*nnext = headNode.frst.*nnext
  all node : (Node - n) | node.nnext' = node.nnext && node.nprev' = node.nprev
}

pred OinsertLst[n:ONode, hn:OHeadNode]{
  -- Pre-conditions
  -- Pre 1 - 'n' is not already in the list
  n ! in hn.frst.*nnext
  -- Pre 2 - 'n' is not attached to any list
  n ! in HeadNode.frst.*nnext
  -- Pre 3 - verify if the n.nnext and n.nprev are none
  n.nnext = none  && n.nprev = none
  -- Pre 4 - hn is not empty
  hn.frst != none && hn.lst != none
  -- Pre 5 - Id of lst is lower than the Id of n 
  n.id.gt[hn.lst.id]

  -- Post-conditions
  -- Post 3 - The 'n' becomes the 'nnext' of the old 'lst'
  hn.lst.nnext' = n
  -- Post 2 - The old 'lst' becomes the 'nprev' of 'n'
  n.nprev' = hn.lst
  -- Post 4 - The new lst has the nnext set to none
  n.nnext' = none
  -- Post 1 - 'n' becomes the new 'lst' of 'hn'
  hn.lst' = n

  -- Frame-conditions
  -- Frame 1 - 'nprev' and 'nnext' relationships of other nodes do not change
  all node: Node - (n + hn.lst) |  node.nprev' = node.nprev and node.nnext' = node.nnext
  -- Frame 2 - 'frst' of 'hn' does not change
  hn.frst' = hn.frst
  -- Frame 3 - all previous nodes remain the same
  all node:Node - (n) | node.nprev' = node.nprev
  -- Frame 4 - everything stays the same for the rest of the headNodes
  all headNode : (HeadNode - hn) | headNode.frst' = headNode.frst and headNode.lst' = headNode.lst
}

pred OinsertFrst[n:ONode, hn:OHeadNode]{

  -- Pre-conditions
  -- Pre 1 - 'n' is not already in the list
  n ! in hn.frst.*nnext
  -- Pre 2 - 'n' is not attached to any list
  n ! in HeadNode.frst.*nnext
  -- Pre 3 - verify if the n.nnext and n.nprev are none
  n.nnext = none  && n.nprev = none
  -- Pre 4 - hn is not empty
  hn.frst != none && hn.lst != none
  -- Pre 5 - Id of frst is higher than the Id of n
  n.id.lt[hn.frst.id]

  -- Post-conditions
  -- Post 3 - The 'n' becomes the 'nnext' of the old 'lst'
  hn.frst.nprev' = n
  -- Post 2 - The old 'lst' becomes the 'nprev' of 'n'
  n.nnext' = hn.frst
  -- Post 4 - The new lst has the nnext set to none
  n.nprev' = none
  -- Post 1 - 'n' becomes the new 'lst' of 'hn'
  hn.frst' = n

  -- Frame-conditions
  -- Frame 1 - 'nprev' and 'nnext' relationships of other nodes do not change
  all node: Node - (n + hn.frst) |  node.nprev' = node.nprev and node.nnext' = node.nnext
  -- Frame 2 - 'frst' of 'hn' does not change
  hn.lst' = hn.lst
  -- Frame 3 - all previous nodes remain the same
  all node:Node - (n) | node.nnext' = node.nnext
  -- Frame 4 - everything stays the same for the rest of the headNodes
  all headNode : (HeadNode - hn) | headNode.frst' = headNode.frst and headNode.lst' = headNode.lst
}

pred OinsertMiddle[n:ONode, hn:OHeadNode]{
  -- Pre-conditions
  -- Pre 1 - 'n' is not already in the list
  n ! in hn.frst.*nnext
  -- Pre 2 - 'n' is not attached to any list
  n ! in HeadNode.frst.*nnext
  -- Pre 3 - verify if the n.nnext and n.nprev are none
  n.nnext = none  && n.nprev = none
  -- Pre 4 - hn is not empty
  hn.frst != none && hn.lst != none
  -- Pre 5 - Id of frst is higher than the Id of n
  n.id.gt[hn.frst.id] && n.id.lt[hn.lst.id]


  all node : hn.frst.*nnext  | n.id.gt[node.id] and n.id.lt[node.nnext.id] implies ( 
                                                                                  -- Post1 
                                                                                  node.nnext' = n and
                                                                                  -- Post2
                                                                                  node.nnext.nprev' = n and
                                                                                  -- Post3
                                                                                  n.nnext' = node.nnext and
                                                                                  -- Post4
                                                                                  n.nprev' = node)

  -- Frame-conditions
  -- Frame 1 - 'nprev' and 'nnext' relationships of other nodes do not change
  all node:  hn.frst.*nnext  - hn.lst - hn.frst | !(n.id.gt[node.id] and n.id.lt[node.nnext.id]) implies node.nprev' = node.nprev and node.nnext' = node.nnext
  -- Frame 2 - 'frst' of 'hn' does not change
  hn.lst' = hn.lst and hn.frst' = hn.frst
  -- Frame 3 - all the others Nodes from the others HeadNodes stay the same 
  all node: Node - n  | node !in hn.frst.*nnext implies node.nprev' = node.nprev and node.nnext' = node.nnext
  -- Frame 4 - everything stays the same for the rest of the headNodes
  all headNode : (HeadNode - hn) | headNode.frst' = headNode.frst and headNode.lst' = headNode.lst
  -- Frame5 - what stays the for the n.nprev and n.nnext
  all node : hn.frst.*nnext  | n.id.gt[node.id] and n.id.lt[node.nnext.id] implies (node.nprev' = node.nprev and node.nnext.nnext' = node.nnext.nnext) 
  
}

-- Remove
// Same as the exercise 3 included in open Ex3

// Ex 4.4
run {
  (eventually some hn:OHeadNode, n:ONode | Oinsert[n,hn]) 
  and
  (eventually some hn:OHeadNode, n:ONode | remove[n,hn])
}