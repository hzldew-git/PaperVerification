(* Command-line entry point; the reusable .m package never exits the kernel. *)
Get[FileNameJoin[{DirectoryName[$InputFileName], "TraceEuclideanVerification.m"}]];
result = TraceEuclideanVerification`RunVerification[];
If[FailureQ[result], Print[result]; Exit[1]];
Exit[If[TrueQ[Lookup[result, "all_passed", Lookup[result, "pass", False]]], 0, 1]];
