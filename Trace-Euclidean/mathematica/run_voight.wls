(* Optional archived-row checks; uses the same reusable .m package. *)
Get[FileNameJoin[{DirectoryName[$InputFileName], "TraceEuclideanVerification.m"}]];
result = TraceEuclideanVerification`RunVoightIntegrity[];
If[FailureQ[result], Print[result]; Exit[1]];
Exit[If[TrueQ[Lookup[result, "pass", False]], 0, 1]];
