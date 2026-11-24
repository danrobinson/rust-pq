"""Recognize the Rust control flow interpreted by PeerEquality.Wots."""


def check(exact, scoped, compact, source):
    for decl in ("const LOG_W:usize=4;", "const W:u32=16;", "const CK_LEN:usize=3;"):
        if compact(source).count(compact(decl)) != 1:
            raise ValueError(f"unsupported WOTS constant {decl}")
    exact("util", "base_2b", """
        debug_assert!(x.len()>=(OutLen::USIZE*B::USIZE).div_ceil(8));debug_assert!(B::USIZE<=16);
        let mut bits=0usize;let mut i=0;let mut total=0usize;
        Array::<u16,OutLen>::from_fn(|_:usize|{
        while bits<B::USIZE{total=(total<<8)+x[i] as usize;bits+=8;i+=1;}
        bits-=B::USIZE;let out=(total>>bits)&((1<<B::U8)-1);total&=(1<<bits)-1;
        out.try_into().expect("B is less than 16")})
    """)
    exact("wots", "wots_chain", """
        debug_assert!(i+s<1<<LOG_W,"Invalid wots_chain index");
        let mut tmp=x.clone();let mut adrs=adrs.clone();for j in i..(i+s){
        adrs.hash_adrs.set(j);tmp=self.f(&adrs,&tmp);}tmp
    """)
    ds = """
        let msg=base_2b::<Self::WotsMsgLen,U<LOG_W>>(m.as_slice());
        let csum=msg.iter().map(|&x|(1<<LOG_W)-1-x).sum::<u16>()<<4;
        let csum_bytes=csum.to_be_bytes();let csum_chunks=base_2b::<U<CK_LEN>,U<LOG_W>>(&csum_bytes);
        let mut msg_csum=msg.iter().chain(csum_chunks.iter());
    """
    secret = """
        let i:u32=i.try_into().expect("i is less than 2^32");
        sk_adrs.chain_adrs.set(i);adrs.chain_adrs.set(i);let sk=self.prf_sk(sk_seed,&sk_adrs);
    """
    setup = "let mut adrs=adrs.clone();let mut sk_adrs=adrs.prf_adrs();"
    array = "Array::<Array<u8,Self::N>,Self::WotsSigLen>::from_fn(|i:usize|{"
    exact("wots", "wots_pk_gen", setup + "let tmp=" + array + secret + """
        self.wots_chain(&sk,0,(1<<LOG_W)-1,&adrs)});
        let pk_adrs=adrs.pk_adrs();self.t(&pk_adrs,&tmp)
    """)
    exact("wots", "wots_sign", ds + setup + "let sig=" + array + secret + """
        self.wots_chain(&sk,0,u32::from(*msg_csum.next().unwrap()),&adrs)});WotsSig(sig)
    """)
    exact("wots", "wots_pk_from_sig", ds + "let mut adrs=adrs.clone();let tmp=" + array + """
        adrs.chain_adrs.set(i.try_into().expect("i is less than 2^32"));
        let msg_i=u32::from(*msg_csum.next().unwrap());
        self.wots_chain(&sig.0[i],msg_i,W-1-msg_i,&adrs)});self.t(&adrs.pk_adrs(),&tmp)
    """)
    prefix = "layer_adrs:self.layer_adrs,tree_adrs_low:self.tree_adrs_low,tree_adrs_high:self.tree_adrs_high,"
    for method, ty, tail in (("prf_adrs", "WotsPrf", "chain_adrs:0.into(),hash_adrs:0.into(),"),
                             ("pk_adrs", "WotsPk", "padding:0.into(),")):
        scoped("address", r"impl WotsHash\b", method, ty + "{" + prefix +
               "type_const:" + ty + "::TYPE_CONST.into(),key_pair_adrs:self.key_pair_adrs," + tail + "}")
