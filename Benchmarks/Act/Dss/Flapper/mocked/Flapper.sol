// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.28;

contract FlapperNoop {
    function vatMove(address, address, uint256) external {}
    function gemMove(address, address, uint256) external {}
}

contract FlapperMocked {
    mapping(address => uint256) public wards;
    mapping(uint256 => uint256) public bid;
    mapping(uint256 => uint256) public lot;
    mapping(uint256 => address) public guy;
    uint256 public kicks;
    uint256 public live;
    uint256 public lid;
    uint256 public fill;
    FlapperNoop public mock;
    modifier auth() { require(wards[msg.sender] == 1); _; }
    constructor(address mock_) { wards[msg.sender] = 1; live = 1; mock = FlapperNoop(mock_); }
    function rely(address usr) external auth { wards[usr] = 1; }
    function deny(address usr) external auth { wards[usr] = 0; }
    function fileLid(uint256 data) external auth { lid = data; }
    function kick(uint256 lot_, uint256 bid_) external auth returns (uint256 id) {
        require(live == 1);
        fill += lot_;
        require(fill <= lid);
        id = ++kicks;
        mock.vatMove(msg.sender, address(this), lot_);
    }
    function cage(uint256 rad) external auth { live = 0; mock.vatMove(address(this), msg.sender, rad); }
}
