type Actual = crate::PEER_TYPE;
#[derive(Clone, Debug)]
struct P([u8; N]);
impl WotsParams for P {
    type WotsMsgLen = <Actual as WotsParams>::WotsMsgLen;
    type WotsSigLen = <Actual as WotsParams>::WotsSigLen;
}
impl XmssParams for P {
    type HPrime = <Actual as XmssParams>::HPrime;
}
impl HypertreeParams for P {
    type D = <Actual as HypertreeParams>::D;
    type H = <Actual as HypertreeParams>::H;
}
macro_rules! params { ($($body:tt)*) => { impl ForsParams for P {
    type A = <Actual as ForsParams>::A;
    type K = <Actual as ForsParams>::K;
    type MD = <Actual as ForsParams>::MD;
    $($body)*
} }; }
