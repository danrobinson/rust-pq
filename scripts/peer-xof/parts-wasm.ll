B0:
v0 = icmp eq i32 length, 0
br i1 v0, label B9, label B1
B1:
v1 = phi i32 [ v2, B8 ], [ 0, B0 ]
v3 = getelementptr inbounds nuw [8 x i8], ptr out, i32 v1
v4 = load ptr, ptr v3, align 4
v5 = getelementptr i8, ptr v3, i32 4
v6 = load i32, ptr v5, align 4
v7 = icmp eq i32 v6, 0
br i1 v7, label B8, label B2
B2:
v8 = and i32 v6, 3
v9 = icmp ult i32 v6, 4
br i1 v9, label B6, label B3
B3:
v10 = and i32 v6, -4
br label B4
B4:
v11 = phi i32 [ 0, B3 ], [ v12, B4 ]
v13 = phi i32 [ 0, B3 ], [ v14, B4 ]
v15 = getelementptr inbounds nuw [8 x i8], ptr v4, i32 v11
v16 = load ptr, ptr v15, align 4
v17 = getelementptr i8, ptr v15, i32 4
v18 = load i32, ptr v17, align 4
tail call void produce(ptr noundef nonnull v16, i32 noundef v18)
v19 = getelementptr inbounds nuw [8 x i8], ptr v4, i32 v11
v20 = getelementptr inbounds nuw i8, ptr v19, i32 8
v21 = load ptr, ptr v20, align 4
v22 = getelementptr i8, ptr v19, i32 12
v23 = load i32, ptr v22, align 4
tail call void produce(ptr noundef nonnull v21, i32 noundef v23)
v24 = getelementptr inbounds nuw [8 x i8], ptr v4, i32 v11
v25 = getelementptr inbounds nuw i8, ptr v24, i32 16
v26 = load ptr, ptr v25, align 4
v27 = getelementptr i8, ptr v24, i32 20
v28 = load i32, ptr v27, align 4
tail call void produce(ptr noundef nonnull v26, i32 noundef v28)
v29 = getelementptr inbounds nuw [8 x i8], ptr v4, i32 v11
v30 = getelementptr inbounds nuw i8, ptr v29, i32 24
v31 = load ptr, ptr v30, align 4
v32 = getelementptr i8, ptr v29, i32 28
v33 = load i32, ptr v32, align 4
tail call void produce(ptr noundef nonnull v31, i32 noundef v33)
v12 = add nuw nsw i32 v11, 4
v14 = add i32 v13, 4
v34 = icmp eq i32 v14, v10
br i1 v34, label v35-lcssa, label B4
B5:
v36 = icmp eq i32 v8, 0
br i1 v36, label B8, label B6
B6:
v37 = phi i32 [ 0, B2 ], [ v12, v35-lcssa ]
v38 = icmp ne i32 v8, 0
tail call void @llvm.assume(i1 v38)
br label B7
B7:
v39 = phi i32 [ v40, B7 ], [ v37, B6 ]
v41 = phi i32 [ v42, B7 ], [ 0, B6 ]
v43 = getelementptr inbounds nuw [8 x i8], ptr v4, i32 v39
v44 = load ptr, ptr v43, align 4
v45 = getelementptr i8, ptr v43, i32 4
v46 = load i32, ptr v45, align 4
tail call void produce(ptr noundef nonnull v44, i32 noundef v46)
v40 = add nuw nsw i32 v39, 1
v42 = add i32 v41, 1
v47 = icmp eq i32 v42, v8
br i1 v47, label B8, label B7
B8:
v2 = add nuw nsw i32 v1, 1
v48 = icmp eq i32 v2, length
br i1 v48, label B9, label B1
B9:
ret void