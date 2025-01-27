import { Application } from '@yowasp/runtime';
import { instantiate } from '../gen/spade.js';

export { Exit } from '@yowasp/runtime';

const spade = new Application(() => import('./resources-spade.js'), instantiate, 'yowasp-spade');
const runSpade = spade.run.bind(spade);

export { runSpade };
export const commands = { 'spade': runSpade };
