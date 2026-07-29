permit(
  principal in a::"\0\0:\0 \0\0\0\0\0\0\0\0",
  action == Action::"",
  resource in a::"\0\0:\0 \0\0\0\0\0\0\0\0"
) when {
  (true && ([].contains((if false then {"in": context} else {"in": {}})["in"]))) && false
};
