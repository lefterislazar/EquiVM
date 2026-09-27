pragma solidity ^0.8.28;
contract VowVat { uint256 public healed; function heal(uint256 rad) external{healed+=rad;} }
contract VowFlapper {
 uint256 public kicks; uint256 public cages;
 function kick(uint256,uint256) external returns(uint256 id){id=++kicks;}
 function cage(uint256) external{cages+=1;}
}
contract VowFlopper {
 uint256 public kicks; uint256 public cages;
 function kick(address,uint256,uint256) external returns(uint256 id){id=++kicks;}
 function cage() external{cages+=1;}
}
contract VowStandalone {
 mapping(address=>uint256) public wards; uint256 public Ash; uint256 public wait; uint256 public dump; uint256 public sump; uint256 public bump; uint256 public hump; uint256 public live;
 VowVat public vat; VowFlapper public flapper; VowFlopper public flopper;
 modifier auth(){require(wards[msg.sender]==1);_;}
 constructor(address vat_,address flapper_,address flopper_){require(vat_!=flapper_&&vat_!=flopper_&&flapper_!=flopper_);wards[msg.sender]=1;live=1;vat=VowVat(vat_);flapper=VowFlapper(flapper_);flopper=VowFlopper(flopper_);}
 function rely(address u) external auth{require(live==1);wards[u]=1;} function deny(address u) external auth{wards[u]=0;}
 function fileWait(uint256 x) external auth{wait=x;} function fileDump(uint256 x) external auth{dump=x;} function fileSump(uint256 x) external auth{sump=x;} function fileBump(uint256 x) external auth{bump=x;} function fileHump(uint256 x) external auth{hump=x;}
 function heal(uint256 rad) external{vat.heal(rad);}
 function flop() external returns(uint256 id){require(live==1);Ash+=sump;id=flopper.kick(address(this),dump,sump);}
 function flap() external returns(uint256 id){require(live==1);id=flapper.kick(bump,0);}
 function cage() external auth{require(live==1);live=0;Ash=0;flapper.cage(0);flopper.cage();vat.heal(0);}
}
