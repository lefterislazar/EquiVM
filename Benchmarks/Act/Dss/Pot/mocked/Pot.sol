// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.28;

contract PotNoop {
    function move(address, address, uint256) external {}
}

contract PotMocked {
    mapping(address => uint256) public wards;
    mapping(address => uint256) public pie;
    uint256 public Pie;
    uint256 public chi;
    uint256 public live;
    PotNoop public mock;

    uint256 internal constant ONE = 10 ** 27;

    modifier auth() {
        require(wards[msg.sender] == 1);
        _;
    }

    constructor(address mock_) {
        wards[msg.sender] = 1;
        chi = ONE;
        live = 1;
        mock = PotNoop(mock_);
    }

    function rely(address usr) external auth { wards[usr] = 1; }
    function deny(address usr) external auth { wards[usr] = 0; }
    function cage() external auth { live = 0; }

    function join(uint256 wad) external {
        pie[msg.sender] += wad;
        Pie += wad;
        mock.move(msg.sender, address(this), chi * wad);
    }

    function exit(uint256 wad) external {
        pie[msg.sender] -= wad;
        Pie -= wad;
        mock.move(address(this), msg.sender, chi * wad);
    }
}
