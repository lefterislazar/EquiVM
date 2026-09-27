pragma solidity ^0.8.28;

contract CatVat {
    uint256 public grabs;
    function grab(bytes32, address, address, address, int256, int256) external { grabs += 1; }
}

contract CatVow {
    uint256 public fessed;
    function fess(uint256 rad) external { fessed += rad; }
}

contract CatFlipper {
    uint256 public kicks;
    function kick(address, address, uint256, uint256, uint256) external returns (uint256 id) { id = ++kicks; }
}

contract CatStandalone {
    mapping(address => uint256) public wards;
    mapping(bytes32 => uint256) public ilkChop;
    mapping(bytes32 => uint256) public ilkDunk;
    uint256 public live;
    uint256 public box;
    uint256 public litter;
    CatVat public vat;
    CatVow public vow;
    CatFlipper public flip;
    uint256 constant RAY = 10 ** 27;
    modifier auth() { require(wards[msg.sender] == 1); _; }

    constructor(address vat_, address vow_, address flip_) {
        require(vat_ != vow_ && vat_ != flip_ && vow_ != flip_);
        wards[msg.sender] = 1; live = 1;
        vat = CatVat(vat_); vow = CatVow(vow_); flip = CatFlipper(flip_);
    }
    function rely(address u) external auth { wards[u] = 1; }
    function deny(address u) external auth { wards[u] = 0; }
    function fileBox(uint256 x) external auth { box = x; }
    function fileIlk(bytes32 ilk, uint256 chop, uint256 dunk) external auth { ilkChop[ilk] = chop; ilkDunk[ilk] = dunk; }
    function claw(uint256 x) external auth { litter -= x; }
    function cage() external auth { live = 0; }
    function bite(bytes32 ilk, address urn) external returns (uint256 id) {
        require(live == 1 && ilkDunk[ilk] != 0 && ilkChop[ilk] != 0);
        require(box - litter >= RAY);
        vat.grab(ilk, urn, address(this), address(vow), -int256(1), -int256(1));
        vow.fess(RAY);
        litter += RAY;
        id = flip.kick(urn, address(vow), RAY, 1, 0);
    }
}
