(* Batch wrapper. The .m file itself does not exit the kernel, so it is safe to
   load interactively in Mathematica. *)
Get[FileNameJoin[{DirectoryName[$InputFileName], "verify_trace_euclidean_v9.m"}]];
Exit[$VerificationExitCode];
