import pandas as pd
import seaborn as sns
from matplotlib import pyplot as plt

df_times = pd.read_csv('cmake-build-debug/times.csv', index_col=0)

a = df_times.to_numpy()

a.sort(axis=1)

for y in range(len(a)):
    for x in range(len(a[0])):
        if x > 0:
            a[y, x] = a[y, x] + a[y, x - 1]

df_times.replace(a)

df_times = df_times.transpose() / 60000

sns_plot_times = sns.lineplot(data=df_times, markers=True, dashes=False)
sns_plot_times.set(xlabel='Problems solved', ylabel='Cumulative computation time [min]', xticks=[2*i for i in range((1+len(a[0]))//2)])

fiugre_times = sns_plot_times.get_figure()

fiugre_times.savefig("cactus-times.png")
