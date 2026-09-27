// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.28;

contract DaiJoinNoop {
    function vatMove(address, address, uint256) external {}
    function burn(address, uint256) external {}
    function mint(address, uint256) external {}
}

contract DaiJoinMocked {
    mapping(address => uint256) public wards;
    DaiJoinNoop public mock;
    uint256 public live;

    uint256 internal constant ONE = 10 ** 27;

    modifier auth() {
        require(wards[msg.sender] == 1);
        _;
    }

    constructor(address mock_) {
        wards[msg.sender] = 1;
        mock = DaiJoinNoop(mock_);
        live = 1;
    }

    function rely(address usr) external auth { wards[usr] = 1; }
    function deny(address usr) external auth { wards[usr] = 0; }
    function cage() external auth { live = 0; }

    function join(address usr, uint256 wad) external {
        uint256 rad = ONE * wad;
        mock.vatMove(address(this), usr, rad);
        mock.burn(msg.sender, wad);
    }

    function exit(address usr, uint256 wad) external {
        require(live == 1);
        uint256 rad = ONE * wad;
        mock.vatMove(msg.sender, address(this), rad);
        mock.mint(usr, wad);
    }
}
