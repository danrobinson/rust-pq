B0:
v0 = mul nuw nsw i64 length, 136
v1 = getelementptr inbounds nuw i8, ptr out, i64 v0
v2 = icmp eq i64 length, 0
br i1 v2, label B2, label B1
B1:
v3 = phi ptr [ v4, B1 ], [ out, B0 ]
v4 = getelementptr inbounds nuw i8, ptr v3, i64 136
tail call void produce(ptr noundef nonnull v3)
v5 = icmp eq ptr v4, v1
br i1 v5, label B2, label B1
B2:
ret void
