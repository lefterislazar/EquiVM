pragma solidity ^0.8.28;
contract DaiJoinVat { uint256 public moved; function move(address,address,uint256 rad) external { moved += rad; } }
contract DaiJoinDai { uint256 public minted; uint256 public burned; function mint(address,uint256 wad) external { minted += wad; } function burn(address,uint256 wad) external { burned += wad; } }
contract DaiJoinStandalone {
    mapping(address=>uint256) public wards; uint256 public live; DaiJoinVat public vat; DaiJoinDai public dai;
    uint256 constant ONE=10**27; modifier auth(){require(wards[msg.sender]==1);_;}
    constructor(address vat_,address dai_){require(vat_!=dai_);wards[msg.sender]=1;live=1;vat=DaiJoinVat(vat_);dai=DaiJoinDai(dai_);}
    function rely(address u) external auth{wards[u]=1;} function deny(address u) external auth{wards[u]=0;} function cage() external auth{live=0;}
    function join(address u,uint256 wad) external{uint256 rad=ONE*wad;vat.move(address(this),u,rad);dai.burn(msg.sender,wad);}
    function exit(address u,uint256 wad) external{require(live==1);uint256 rad=ONE*wad;vat.move(msg.sender,address(this),rad);dai.mint(u,wad);}
}
