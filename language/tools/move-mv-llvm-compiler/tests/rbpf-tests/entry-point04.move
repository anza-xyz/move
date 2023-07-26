// input entry-point04.json

module 0xa000::entry_point {

    public entry fun bar(): u64 {
        0
    }

    public entry fun foo(): u64 {
        17
    }

    public entry fun transfer(
        sender: &signer,
        receiver: address,
        amount: u64,
    ): u64
    {
        assert!(amount == 0x2b29251f1d171311, 0xf000);
        0
    }
}
