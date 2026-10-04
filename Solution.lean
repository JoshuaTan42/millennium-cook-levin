import Comp
import CookLevin
import SatInP
import Pkg

theorem p_eq_np : Millennium.ClayPVersusNP :=
  Millennium.ClayPVersusNP.nondeterministic_polynomial_time_complete_in_polynomial_time
    PvsNP.comp PvsNP.cook_levin PvsNP.sat_in_p
