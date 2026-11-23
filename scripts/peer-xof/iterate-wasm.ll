B0:
v0 = mul nuw nsw i32 length, 136
v1 = getelementptr inbounds nuw i8, ptr out, i32 v0
v2 = icmp eq i32 length, 0
br i1 v2, label B5, label B1
B1:
v3 = add nuw nsw i32 length, 536870911
v4 = and i32 v3, 536870911
v5 = and i32 length, 7
v6 = icmp eq i32 v5, 0
br i1 v6, label B3, label B2
B2:
v7 = phi ptr [ v8, B2 ], [ out, B1 ]
v9 = phi i32 [ v10, B2 ], [ 0, B1 ]
v8 = getelementptr inbounds nuw i8, ptr v7, i32 136
tail call void produce(ptr noundef nonnull v7)
v10 = add i32 v9, 1
v11 = icmp eq i32 v10, v5
br i1 v11, label B3, label B2
B3:
v12 = phi ptr [ out, B1 ], [ v8, B2 ]
v13 = icmp samesign ult i32 v4, 7
br i1 v13, label B5, label B4
B4:
v14 = phi ptr [ v15, B4 ], [ v12, B3 ]
v16 = getelementptr inbounds nuw i8, ptr v14, i32 136
tail call void produce(ptr noundef nonnull v14)
v17 = getelementptr inbounds nuw i8, ptr v14, i32 272
tail call void produce(ptr noundef nonnull v16)
v18 = getelementptr inbounds nuw i8, ptr v14, i32 408
tail call void produce(ptr noundef nonnull v17)
v19 = getelementptr inbounds nuw i8, ptr v14, i32 544
tail call void produce(ptr noundef nonnull v18)
v20 = getelementptr inbounds nuw i8, ptr v14, i32 680
tail call void produce(ptr noundef nonnull v19)
v21 = getelementptr inbounds nuw i8, ptr v14, i32 816
tail call void produce(ptr noundef nonnull v20)
v22 = getelementptr inbounds nuw i8, ptr v14, i32 952
tail call void produce(ptr noundef nonnull v21)
v15 = getelementptr inbounds nuw i8, ptr v14, i32 1088
tail call void produce(ptr noundef nonnull v22)
v23 = icmp eq ptr v15, v1
br i1 v23, label B5, label B4
B5:
ret void