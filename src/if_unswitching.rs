
use crate::util::BlockIter;
fn unswitch_if<'c, 'a>(outer_block: BlockRef<'c, 'a>){
    for if_statement in BlockIter::new(outer_block){
        let ident = if_statement.name();
        let name = ident.as_string_ref().as_str().unwrap();
        if name != "scf.if"{
            continue
        }
        let true_block = if_statement.region(0).unwrap();
        let false_block = if_statement.region(1).unwrap();
        if if_statement.next_in_block().is_none(){
            return
        }
        let rewriter = IrRewriter::from_op(if_statement).as_rewriter_base();
        for op in BlockIter::from_operation(if_statement).skip(1){
            
        }
        
    }
}