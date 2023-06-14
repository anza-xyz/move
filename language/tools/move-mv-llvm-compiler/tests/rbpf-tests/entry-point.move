// input entry-point.json

module 0xa000::entry_point {

    public entry fun transfer(
        /*sender: &signer,
        receiver: address,
        amount: u64,*/
    ): u64
    {
        //assert!(amount == 1234, 0xf000);
        0
    }

    public entry fun dummy(): u64 {
        0
    }

    public entry fun zzz(): u64 {
        17
    }
}
