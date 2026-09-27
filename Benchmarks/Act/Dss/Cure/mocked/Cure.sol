// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.28;

contract CureNoop {
    function cure(address) external pure returns (uint256) { return 1; }
}

contract CureMocked {
    mapping(address => uint256) public wards;
    mapping(address => uint256) public pos;
    mapping(address => uint256) public amt;
    mapping(address => uint256) public loaded;
    uint256 public sourceCount;
    uint256 public lCount;
    uint256 public say;
    uint256 public live;
    uint256 public wait;
    CureNoop public mock;

    modifier auth() { require(wards[msg.sender] == 1); _; }

    constructor(address mock_) {
        wards[msg.sender] = 1;
        live = 1;
        mock = CureNoop(mock_);
    }

    function rely(address usr) external auth { require(live == 1); wards[usr] = 1; }
    function deny(address usr) external auth { require(live == 1); wards[usr] = 0; }
    function fileWait(uint256 value) external auth { require(live == 1); wait = value; }

    function lift(address src) external auth {
        require(live == 1 && pos[src] == 0);
        sourceCount += 1;
        pos[src] = 1;
    }

    function drop(address src) external auth {
        require(live == 1 && pos[src] != 0);
        pos[src] = 0;
        amt[src] = 0;
        sourceCount -= 1;
    }

    function cage() external auth { require(live == 1); live = 0; }

    function tell() external view returns (uint256) {
        require(live == 0 && lCount == sourceCount);
        return say;
    }

    function load(address src) external {
        require(live == 0 && pos[src] != 0);
        uint256 oldAmount = amt[src];
        uint256 newAmount = mock.cure(src);
        amt[src] = newAmount;
        say = say - oldAmount + newAmount;
        if (loaded[src] == 0) {
            loaded[src] = 1;
            lCount += 1;
        }
    }
}
