// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.28;

contract GemJoinNoop {
    function decimals() external pure returns (uint256) { return 18; }
    function slip(bytes32, address, int256) external {}
    function transferFrom(address, address, uint256) external pure returns (bool) { return true; }
    function transfer(address, uint256) external pure returns (bool) { return true; }
}

contract GemJoinMocked {
    mapping(address => uint256) public wards;
    GemJoinNoop public mock;
    bytes32 public ilk;
    uint256 public dec;
    uint256 public live;

    modifier auth() {
        require(wards[msg.sender] == 1);
        _;
    }

    constructor(address mock_, bytes32 ilk_) {
        wards[msg.sender] = 1;
        mock = GemJoinNoop(mock_);
        ilk = ilk_;
        dec = mock.decimals();
        live = 1;
    }

    function rely(address usr) external auth { wards[usr] = 1; }
    function deny(address usr) external auth { wards[usr] = 0; }
    function cage() external auth { live = 0; }

    function join(address usr, uint256 wad) external {
        require(live == 1);
        require(wad <= uint256(type(int256).max));
        mock.slip(ilk, usr, int256(wad));
        require(mock.transferFrom(msg.sender, address(this), wad));
    }

    function exit(address usr, uint256 wad) external {
        require(wad <= uint256(type(int256).max));
        mock.slip(ilk, msg.sender, -int256(wad));
        require(mock.transfer(usr, wad));
    }
}
