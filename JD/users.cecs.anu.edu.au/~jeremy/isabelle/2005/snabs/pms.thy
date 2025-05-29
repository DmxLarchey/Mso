
theory pms imports pmsdef mso begin 

consts
  leaves :: "spms rtree => symb list"
  leavess :: "spms rtree list => symb list"

primrec
  leavess_Nil : "leavess [] = []"
  leavess_Cons : "leavess (t # ts) = leaves t @ leavess ts"

  leaves_def : "leaves (Node s ts) = 
    (case s of Leaf a => [a] | Inner => leavess ts)" 
  
end 

