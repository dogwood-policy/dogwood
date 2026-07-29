permit(
  principal,
  action in [Action::"action"],
  resource is a in a::""
) when {
  ((true && ([].contains(if (a::"" in action) then [] else [[(datetime("9087-12-06T23:11:11.087+1111")).offset(duration("-4\u{82}29771061636907073d7591775290867564479h")), datetime("0000-01-01"), datetime("0000-01-01")], [], []]))) && false) && false
};
