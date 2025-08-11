use spade_common::location_info::Loc;
use spade_hir::{domains::DomainName, Unit};

use crate::{DomainState, DomainVar, DomainedExpression, Result};

impl DomainState {
    fn visit_unit(&mut self, unit: &Loc<Unit>) -> Result<()> {
        for domain in &unit.head.domains {
            let var = self.add_domain_var(DomainVar::Known(domain.clone()));
            let name = match &domain.name {
                DomainName::Annonymous => DomainedExpression::AnnonymousOuter(unit.loc()),
                DomainName::Named(name) => DomainedExpression::Name(name.clone()),
            };
            self.equations.insert(name, var);
        }

        Ok(())
    }
    
}
