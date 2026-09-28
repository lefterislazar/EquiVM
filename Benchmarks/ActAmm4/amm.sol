pragma solidity >=0.8.0;

//interface Token {
//  function balanceOf(address) external view returns (uint256);
//  function transferFrom(address from, address to, uint256 value) external returns (uint);
//  function transfer(uint256 value, address to) external returns (uint);
//}
contract Token {
    uint256 public totalSupply;
    mapping (address => uint256) public balanceOf;
    mapping (address => mapping (address => uint256)) public allowance;

    constructor(uint256 _totalSupply) {
        totalSupply = _totalSupply;
        balanceOf[msg.sender] = _totalSupply;
    }


    function approve(address spender, uint256 value) public returns (bool) {
        if(spender != msg.sender) {
            allowance[msg.sender][spender] = value;
        }
        return true;
    }

    function transfer(uint256 value, address to) public returns (bool) {
        balanceOf[msg.sender] = balanceOf[msg.sender] - value;
        balanceOf[to] = balanceOf[to] + value;
        return true;
    }

    function transferFrom(address from, address to, uint256 value) public returns (bool) {
        if(from != msg.sender && allowance[from][msg.sender] != type(uint256).max) {
            allowance[from][msg.sender] = allowance[from][msg.sender] - value;
        }
        balanceOf[from] = balanceOf[from] - value;
        balanceOf[to] = balanceOf[to] + value;
        return true;
    }
}

contract Token0 is Token {
    constructor(uint256 _totalSupply) Token(_totalSupply) {}
}

contract Token1 is Token {
    constructor(uint256 _totalSupply) Token(_totalSupply) {}
}

contract Amm is Token {
    uint256 internal constant MINIMUM_LIQUIDITY = 1000;
    Token token0;
    Token token1;
    uint256 reserve0;
    uint256 reserve1;
    //uint256 totalSupply;
    //mapping(address => uint256) liquidityOf;

    constructor(address t0, address t1, uint256 liquidity) Token(liquidity - MINIMUM_LIQUIDITY) {
        require (t0 != t1);
        token0 = Token(t0);
        token1 = Token(t1);

        require(liquidity*liquidity == token0.balanceOf(address(this)) * token1.balanceOf(address(this)), "Invalid initial liquidity");
        require(liquidity > 0, 'Invalid initial liquidity');
        totalSupply = liquidity;
        balanceOf[address(this)] =  MINIMUM_LIQUIDITY;
        balanceOf[msg.sender] = liquidity - MINIMUM_LIQUIDITY;
        reserve0 = token0.balanceOf(address(this));
        reserve1 = token1.balanceOf(address(this));
    }

    function mint(address to) public returns (uint256 liquidity) {
      require(totalSupply != 0);

      uint256 balance0 = token0.balanceOf(address(this));
      uint256 balance1 = token1.balanceOf(address(this));

      //uint256 product = balance0 * balance1;
      uint256 amount0 = balance0 - reserve0;
      uint256 amount1 = balance1 - reserve1;

      //if (totalSupply == 0) {
      //  liquidity = product - MINIMUM_LIQUIDITY;
      //  require(amount0 > 0 && amount1 > 0, "invalid amounts");

      //  totalSupply += MINIMUM_LIQUIDITY;
      //} else {
      uint256 liq0 = amount0 * totalSupply / reserve0;
      uint256 liq1 = amount1 * totalSupply / reserve1;

      if (liq0 <= liq1) {
        liquidity = liq0;
      } else {
        liquidity = liq1;
      }

      require(liquidity != 0, "Insufficient liquidity");
      totalSupply += liquidity;
      balanceOf[to] += liquidity;

      //kLast = product;
      reserve0 = balance0;
      reserve1 = balance1;
    }

    function burn(uint256 liquidity, address to) public {
      require(totalSupply != 0);

      //uint256 balance0 = token0.balanceOf(address(this));
      //uint256 balance1 = token1.balanceOf(address(this));

      uint256 amount0 = (liquidity * reserve0) / totalSupply;
      uint256 amount1 = (liquidity * reserve1) / totalSupply;

      totalSupply -= liquidity;
      balanceOf[msg.sender] -= liquidity;

      //amount0 = liquidity * balance0 / totalSupply;
      //amount1 = liquidity * balance1 / totalSupply;

      token0.transfer(amount0, to);
      token1.transfer(amount1, to);

      reserve0 = token0.balanceOf(address(this));
      reserve1 = token1.balanceOf(address(this));
    }

    function swap(uint256 amount0Out, uint256 amount1Out, address to) public {
      require(amount0Out > 0 || amount1Out > 0, 'Insufficient output amount');
      require(amount0Out < reserve0 && amount1Out < reserve1, 'Insufficient liquidity');
      require(to != address(token0) && to != address(token1), 'Invalid TO');

      //if(amount0Out > 0)
        token0.transfer(amount0Out, to);
      //if(amount1Out > 0)
        token1.transfer(amount1Out, to);

      uint256 balance0 = token0.balanceOf(address(this));
      uint256 balance1 = token1.balanceOf(address(this));

      uint256 amount0In = balance0 > reserve0 - amount0Out ? balance0 - (reserve0 - amount0Out) : 0;
      uint256 amount1In = balance1 > reserve1 - amount1Out ? balance1 - (reserve1 - amount1Out) : 0;
      require(amount0In > 0 || amount1In > 0, 'Insufficient input amount');

      require(balance0* balance1 >= reserve0 * reserve1, 'K');

      reserve0 = balance0;
      reserve1 = balance1;
    }

}
