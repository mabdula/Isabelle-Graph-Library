(* bfs_api.sml -- the one line of interface in which the BFS export generated from the current library
   differs from the campaign's: bfs_path takes the parent array, the output array and the vertex (the
   campaign's export also took the distance array).  The single-run program calls BFS_API.path. *)
structure BFS_API = struct
  fun path (_ : int array) parents ra v = BFS_CSR.bfs_path parents ra v
end
