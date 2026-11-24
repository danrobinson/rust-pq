B0:
v0 = icmp eq i64 length, 0
br i1 v0, label B4, label B1
B1:
v1 = phi i64 [ v2, B3 ], [ 0, B0 ]
v3 = getelementptr inbounds nuw [16 x i8], ptr out, i64 v1
v4 = load ptr, ptr v3, align 8
v5 = getelementptr i8, ptr v3, i64 8
v6 = load i64, ptr v5, align 8
v7 = icmp eq i64 v6, 0
br i1 v7, label B3, label B2
B2:
v8 = phi i64 [ v9, B2 ], [ 0, B1 ]
v10 = getelementptr inbounds nuw [16 x i8], ptr v4, i64 v8
v11 = load ptr, ptr v10, align 8
v12 = getelementptr i8, ptr v10, i64 8
v13 = load i64, ptr v12, align 8
tail call void produce(ptr noundef nonnull v11, i64 noundef v13)
v9 = add nuw nsw i64 v8, 1
v14 = icmp eq i64 v9, v6
br i1 v14, label B3, label B2
B3:
v2 = add nuw nsw i64 v1, 1
v15 = icmp eq i64 v2, length
br i1 v15, label B4, label B1
B4:
ret void
