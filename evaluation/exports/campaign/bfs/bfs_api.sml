(* bfs_api.sml -- the one line of interface in which the campaign's BFS export differs from the export
   generated from the current library: its bfs_path also takes the distance array.  The single-run
   program calls BFS_API.path. *)
structure BFS_API = struct
  fun path dists parents ra v = BFS_CSR.bfs_path dists parents ra v
end
